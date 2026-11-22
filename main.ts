// mend: apply a model-written edit to a tree of text files (SPEC.md version 1).
// Implements the CLI, output and exit codes, safe paths, format detection, the three
// line-matching tiers, unified diffs, SEARCH/REPLACE blocks, V4A patches and JSON edits.
// Node 22, standard library alone. Run as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set; the last lines
// hand over to the kit's runner.ts, which must stay unchanged.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) { this.line = line; }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) { this.code = code; this.path = path; }
}

const blank = (s: string): boolean => s.trim() === '';
const tEnd = (s: string): string => s.replace(/[ \t]+$/, '');
const tBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const indentOf = (s: string): string => (/^[ \t]*/.exec(s) ?? [''])[0]!;

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

type Shape = { br: string; lines: string[]; final: boolean };
function shape(text: string): Shape {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const lines = text.split(br);
  if (final) lines.pop();
  return { br, lines, final };
}
function joinShape(s: Shape): string {
  return s.lines.length === 0 ? '' : s.lines.join(s.br) + (s.final ? s.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try { if (statSync(p).isFile()) v = readFileSync(p, 'utf8'); } catch { v = null; }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---- section 5: three tiers of line matching ---------------------------------------

function occ(lines: string[], old: string[], tier: number): number[] {
  const norm = tier === 0 ? (x: string) => x : tier === 1 ? tEnd : tBoth;
  const o = old.map(norm);
  const at: number[] = [];
  for (let i = 0; i + old.length <= lines.length; i += 1) {
    let ok = true;
    for (let j = 0; j < old.length; j += 1) {
      if (norm(lines[i + j]!) !== o[j]) { ok = false; break; }
    }
    if (ok) at.push(i);
  }
  return at;
}
function hitAll(lines: string[], old: string[], strict: boolean): { tier: number; at: number[] } | null {
  for (let t = 0; t <= (strict ? 0 : 2); t += 1) {
    const a = occ(lines, old, t);
    if (a.length > 0) return { tier: t, at: a };
  }
  return null;
}
function hitFrom(lines: string[], old: string[], from: number, strict: boolean): { tier: number; at: number[] } | null {
  for (let t = 0; t <= (strict ? 0 : 2); t += 1) {
    const a = occ(lines, old, t).filter((x) => x >= from);
    if (a.length > 0) return { tier: t, at: a };
  }
  return null;
}
type NewLine = { text: string; oi: number; noEOL?: boolean };
/** Build the replacement lines. Context lines are the FILE's matched line, not the patch's. */
function expand(fileLines: string[], old: string[], neu: NewLine[], pos: number, tier: number): string[] {
  const F = indentOf(fileLines[pos] ?? '');
  const P = indentOf(old[0] ?? '');
  return neu.map((e) => {
    if (e.oi >= 0) return fileLines[pos + e.oi] ?? e.text;
    if (tier === 2 && e.text.trim() !== '' && e.text.startsWith(P)) return F + e.text.slice(P.length);
    return e.text;
  });
}
type Body = { kind: 'ctx' | 'old' | 'new' | 'slash'; text: string; noEOL?: boolean };
function bodyOf(rows: Body[]): { old: string[]; neu: NewLine[] } {
  const old: string[] = [];
  const neu: NewLine[] = [];
  rows.forEach((e, k) => {
    if (e.kind === 'ctx') { const oi = old.length; old.push(e.text); neu.push({ text: e.text, oi, noEOL: e.noEOL }); }
    else if (e.kind === 'old') old.push(e.text);
    else if (e.kind === 'new') neu.push({ text: e.text, oi: -1, noEOL: e.noEOL });
  });
  return { old, neu };
}
function markSlash(rows: Body[]): void {
  for (let k = 0; k + 1 < rows.length; k += 1) {
    if ((rows[k]!.kind === 'new' || rows[k]!.kind === 'ctx') && rows[k + 1]!.kind === 'slash') rows[k]!.noEOL = true;
  }
}

// ---- section 6: unified diffs -------------------------------------------------------

type Hunk = { A: number; body: Body[] };
type USection = { oldP: string | null; newP: string | null; named: boolean; create: boolean; del: boolean; hunks: Hunk[] };
function stripPath(s: string): string {
  let p = (s.split('\t')[0] ?? '').trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}
function hunkBody(lines: string[], start: number): { body: Body[]; end: number } {
  const body: Body[] = [];
  let i = start;
  while (i < lines.length) {
    const b = lines[i]!;
    if (b.startsWith('diff --git ') || (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ '))) break;
    if (b.startsWith('\\')) body.push({ kind: 'slash', text: b });
    else if (b.startsWith(' ')) body.push({ kind: 'ctx', text: b.slice(1) });
    else if (b.startsWith('-')) body.push({ kind: 'old', text: b.slice(1) });
    else if (b.startsWith('+')) body.push({ kind: 'new', text: b.slice(1) });
    else if (b === '') body.push({ kind: 'ctx', text: '' });
    else break;
    i += 1;
  }
  while (body.length > 0 && body[body.length - 1]!.kind === 'ctx' && body[body.length - 1]!.text === '') body.pop();
  markSlash(body);
  return { body, end: i };
}
function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  const flush = (): void => { if (cur !== null) sections.push(cur); cur = null; };
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    let m: RegExpExecArray | null;
    if ((m = /^diff --git a\/(.+?) b\/(.+)$/.exec(l)) !== null) {
      flush();
      cur = { oldP: m[1]!, newP: m[2]!, named: false, create: false, del: false, hunks: [] };
      i += 1;
      continue;
    }
    if (l.startsWith('diff --git ')) throw new Exit2(`error: parse ${i + 1}`);
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && cur.hunks.length > 0) flush();
      if (cur === null) cur = { oldP: null, newP: null, named: false, create: false, del: false, hunks: [] };
      cur.oldP = stripPath(l.slice(4));
      cur.newP = stripPath(lines[i + 1]!.slice(4));
      cur.named = true;
      i += 2;
      continue;
    }
    if (l.startsWith('@@')) {
      const hm = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(l);
      if (hm === null || cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const hb = hunkBody(lines, i + 1);
      cur.hunks.push({ A: Number(hm[1]), body: hb.body });
      i = hb.end;
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (l.startsWith('rename from ')) { if (!cur.named) cur.oldP = l.slice(12).trim(); }
      else if (l.startsWith('rename to ')) { if (!cur.named) cur.newP = l.slice(10).trim(); }
      else if (l.startsWith('new file mode')) cur.create = true;
      else if (l.startsWith('deleted file mode')) cur.del = true;
      else if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      i += 1;
      continue;
    }
    i += 1;
  }
  flush();
  const edits: Edit[] = [];
  for (const s of sections) {
    if (s.oldP === null || s.newP === null) throw new Exit2('error: parse 1');
    const oldP = s.oldP;
    const newP = s.newP;
    if (s.del || newP === '/dev/null') {
      edits.push((tree) => {
        if (!safe(oldP)) throw new Fail('unsafe', oldP);
        if (tree.get(oldP) === null) throw new Fail('missing', oldP);
        tree.now.set(oldP, null);
      });
    } else if (s.create || oldP === '/dev/null') {
      edits.push((tree) => {
        if (!safe(newP)) throw new Fail('unsafe', newP);
        if (tree.get(newP) !== null) throw new Fail('exists', newP);
        const out: string[] = [];
        let noEOL = false;
        for (const h of s.hunks) for (const e of h.body) if (e.kind === 'new') { out.push(e.text); noEOL = !!e.noEOL; }
        tree.now.set(newP, out.length === 0 ? '' : out.join('\n') + (noEOL ? '' : '\n'));
      });
    } else {
      const mv = oldP !== newP;
      edits.push((tree) => {
        if (!safe(oldP)) throw new Fail('unsafe', oldP);
        if (mv && !safe(newP)) throw new Fail('unsafe', newP);
        const before = tree.get(oldP);
        if (before === null) throw new Fail('missing', oldP);
        if (mv && tree.get(newP) !== null) throw new Fail('exists', newP);
        const sh = shape(before);
        const fl = sh.lines.slice();
        let final = sh.final;
        let d = 0;
        for (const h of s.hunks) {
          const { old, neu } = bodyOf(h.body);
          if (old.length === 0) {
            const pos = Math.min(h.A + d, fl.length);
            const add = neu.map((e) => e.text);
            fl.splice(pos, 0, ...add);
            if (pos + add.length === fl.length && neu.length > 0 && neu[neu.length - 1]!.noEOL) final = false;
            d += add.length;
            continue;
          }
          const hit = hitAll(fl, old, strict);
          if (hit === null) throw new Fail('no-match', oldP);
          const target = h.A - 1 + d;
          let pos = hit.at[0]!;
          let best = Math.abs(pos - target);
          for (const a of hit.at) {
            const dist = Math.abs(a - target);
            if (dist < best) { pos = a; best = dist; }
          }
          const endsAtEOF = pos + old.length === fl.length;
          const add = expand(fl, old, neu, pos, hit.tier);
          fl.splice(pos, old.length, ...add);
          if (endsAtEOF && neu.length > 0 && neu[neu.length - 1]!.noEOL) final = false;
          d += neu.length - old.length;
        }
        const out = joinShape({ br: sh.br, lines: fl, final });
        tree.now.set(mv ? newP : oldP, out);
        if (mv) { tree.now.set(oldP, null); tree.moves.push([oldP, newP]); }
      });
    }
  }
  return edits;
}

// ---- section 7: SEARCH/REPLACE ------------------------------------------------------

function srEdits(lines: string[], strict: boolean): Edit[] {
  type Block = { path: string; old: string[]; neu: string[] };
  const blocks: Block[] = [];
  let prev: string | null = null;
  let i = 0;
  let floor = 0;
  while (i < lines.length) {
    let si = -1;
    for (let k = i; k < lines.length; k += 1) if (lines[k]!.trimEnd() === '<<<<<<< SEARCH') { si = k; break; }
    if (si < 0) break;
    let path: string | null = null;
    for (let k = si - 1; k >= floor; k -= 1) {
      const t = lines[k]!.trim();
      if (t !== '' && !t.startsWith('```')) { path = t; break; }
    }
    if (path === null) path = prev;
    if (path === null) throw new Exit2(`error: parse ${si + 1}`);
    let ei = si + 1;
    while (ei < lines.length && lines[ei]!.trimEnd() !== '=======') ei += 1;
    if (ei >= lines.length) throw new Exit2(`error: parse ${si + 1}`);
    let ri = ei + 1;
    while (ri < lines.length && lines[ri]!.trimEnd() !== '>>>>>>> REPLACE') ri += 1;
    if (ri >= lines.length) throw new Exit2(`error: parse ${si + 1}`);
    blocks.push({ path, old: lines.slice(si + 1, ei), neu: lines.slice(ei + 1, ri) });
    prev = path;
    floor = ri + 1;
    i = ri + 1;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => (tree) => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.old.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, b.neu.length === 0 ? '' : b.neu.join('\n') + '\n');
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new Fail('missing', b.path);
    const sh = shape(before);
    const hit = hitAll(sh.lines, b.old, strict);
    if (hit === null) throw new Fail('no-match', b.path);
    if (hit.at.length > 1) throw new Fail('ambiguous', b.path);
    const pos = hit.at[0]!;
    const add = expand(sh.lines, b.old, b.neu.map((t) => ({ text: t, oi: -1 })), pos, hit.tier);
    const fl = sh.lines.slice();
    fl.splice(pos, b.old.length, ...add);
    tree.now.set(b.path, joinShape({ br: sh.br, lines: fl, final: sh.final }));
  });
}

// ---- section 8: V4A patches ---------------------------------------------------------

type Chunk = { anchor: string | null; eof: boolean; body: Body[] };
type VSection = { kind: 'add' | 'delete' | 'update'; path: string; moveTo: string | null; addLines: { text: string; real: boolean }[]; chunks: Chunk[]; lineNo: number };
function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0 || lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first < 0 ? 1 : first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last -= 1;
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const isSection = (l: string): boolean => /^\*\*\* (Add|Delete|Update) File:/.test(l);
  const sections: VSection[] = [];
  let i = first + 1;
  while (i < last) {
    if (blank(lines[i]!)) { i += 1; continue; }
    const l = lines[i]!;
    let m: RegExpExecArray | null;
    if ((m = /^\*\*\* Add File:\s*(.*)$/.exec(l)) !== null) {
      const sec: VSection = { kind: 'add', path: m[1]!.trim(), moveTo: null, addLines: [], chunks: [], lineNo: i + 1 };
      i += 1;
      while (i < last && !isSection(lines[i]!)) {
        const b = lines[i]!;
        if (b.startsWith('+')) sec.addLines.push({ text: b.slice(1), real: true });
        else if (b === '') sec.addLines.push({ text: '', real: false });
        else throw new Exit2(`error: parse ${i + 1}`);
        i += 1;
      }
      while (sec.addLines.length > 0 && !sec.addLines[sec.addLines.length - 1]!.real) sec.addLines.pop();
      sections.push(sec);
      continue;
    }
    if ((m = /^\*\*\* Delete File:\s*(.*)$/.exec(l)) !== null) {
      const sec: VSection = { kind: 'delete', path: m[1]!.trim(), moveTo: null, addLines: [], chunks: [], lineNo: i + 1 };
      i += 1;
      while (i < last && !isSection(lines[i]!)) {
        if (!blank(lines[i]!)) throw new Exit2(`error: parse ${i + 1}`);
        i += 1;
      }
      sections.push(sec);
      continue;
    }
    if ((m = /^\*\*\* Update File:\s*(.*)$/.exec(l)) !== null) {
      const sec: VSection = { kind: 'update', path: m[1]!.trim(), moveTo: null, addLines: [], chunks: [], lineNo: i + 1 };
      i += 1;
      if (i < last) {
        const mv = /^\*\*\* Move to:\s*(.*)$/.exec(lines[i]!);
        if (mv !== null) { sec.moveTo = mv[1]!.trim(); i += 1; }
      }
      const rows: { text: string; no: number }[] = [];
      while (i < last && !isSection(lines[i]!)) { rows.push({ text: lines[i]!, no: i + 1 }); i += 1; }
      while (rows.length > 0 && blank(rows[rows.length - 1]!.text)) rows.pop();
      let chunk: Chunk | null = null;
      let closed = false;
      for (const r of rows) {
        const b = r.text;
        if (b.startsWith('@@')) {
          if (chunk !== null) sec.chunks.push(chunk);
          chunk = { anchor: b.slice(2).trim() || null, eof: false, body: [] };
          closed = false;
          continue;
        }
        if (b.trim() === '*** End of File') {
          if (chunk === null) chunk = { anchor: null, eof: false, body: [] };
          chunk.eof = true;
          sec.chunks.push(chunk);
          chunk = null;
          closed = true;
          continue;
        }
        if (closed) throw new Exit2(`error: parse ${r.no}`);
        if (b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b === '') {
          if (chunk === null) chunk = { anchor: null, eof: false, body: [] };
          const kind: Body['kind'] = b === '' || b.startsWith(' ') ? 'ctx' : b.startsWith('-') ? 'old' : 'new';
          chunk.body.push({ kind, text: b === '' ? '' : b.slice(1) });
          continue;
        }
        throw new Exit2(`error: parse ${r.no}`);
      }
      if (chunk !== null) sec.chunks.push(chunk);
      if (sec.chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${sec.lineNo}`);
      sections.push(sec);
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  const edits: Edit[] = [];
  for (const sec of sections) {
    if (sec.kind === 'add') {
      const p = sec.path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, sec.addLines.map((l) => l.text).join('\n') + '\n');
      });
    } else if (sec.kind === 'delete') {
      const p = sec.path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else {
      const p = sec.path;
      const mvTo = sec.moveTo;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (mvTo !== null && !safe(mvTo)) throw new Fail('unsafe', mvTo);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        if (mvTo !== null && tree.get(mvTo) !== null) throw new Fail('exists', mvTo);
        const sh = shape(before);
        const fl = sh.lines.slice();
        let cursor = 0;
        for (const ch of sec.chunks) {
          let from = cursor;
          if (ch.anchor !== null) {
            const hit = hitFrom(fl, [ch.anchor], cursor, strict);
            if (hit === null) throw new Fail('no-match', p);
            from = hit.at[0]! + 1;
            cursor = from;
          }
          const { old, neu } = bodyOf(ch.body);
          let pos: number;
          let add: string[];
          let tier: number;
          if (old.length === 0) {
            pos = ch.eof ? fl.length : Math.min(from, fl.length);
            add = neu.map((e) => e.text);
            tier = 0;
          } else {
            const hit = hitFrom(fl, old, from, strict);
            if (hit === null) throw new Fail('no-match', p);
            let ats = hit.at;
            if (ch.eof) ats = ats.filter((x) => x + old.length === fl.length);
            if (ats.length === 0) throw new Fail('no-match', p);
            pos = ats[0]!;
            tier = hit.tier;
            add = expand(fl, old, neu, pos, tier);
          }
          fl.splice(pos, old.length, ...add);
          cursor = pos + add.length;
        }
        const out = joinShape({ br: sh.br, lines: fl, final: sh.final });
        tree.now.set(mvTo ?? p, out);
        if (mvTo !== null) { tree.now.set(p, null); tree.moves.push([p, mvTo]); }
      });
    }
  }
  return edits;
}

// ---- section 9: JSON edits ----------------------------------------------------------

function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- invocation, output and atomic write --------------------------------------------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = srEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const nmove = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = nmove;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const moved = (o: string, n: string): boolean =>
    tree.original(o) !== null && tree.get(o) === null && tree.original(n) === null && tree.get(n) !== null;
  const rows: { key: string; text: string }[] = [];
  for (const p of [...tree.now.keys()]) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (tree.moves.some(([o, n]) => (o === p || n === p) && moved(o, n))) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const [o, n] of tree.moves) if (moved(o, n)) rows.push({ key: n, text: `R ${o} -> ${n}` });
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out = rows.map((r) => r.text);
  if (!check) {
    for (const [p, now] of tree.now) {
      if (tree.original(p) === now) continue;
      if (now === null) rmSync(p, { force: true });
      else { mkdirSync(dirname(p), { recursive: true }); writeFileSync(p, now); }
    }
  }
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
