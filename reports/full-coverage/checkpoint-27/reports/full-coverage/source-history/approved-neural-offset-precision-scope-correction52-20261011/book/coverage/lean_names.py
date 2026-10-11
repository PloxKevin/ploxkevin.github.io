"""Index source-level public Lean declarations for correspondence checks.

This is a source index, never a substitute for Lean compilation or kernel replay.
Named nested namespace and section scopes are tracked; private and anonymous
instances do not provide externally referenceable names.
"""
import re


def without_comments(text):
    """Mask nested block comments, line comments and string literals, preserving lines."""
    out=[]
    i=0
    depth=0
    string=False
    while i<len(text):
        pair=text[i:i+2]
        c=text[i]
        if depth:
            if pair=='/-':
                depth+=1;out.extend('  ');i+=2;continue
            if pair=='-/':
                depth-=1;out.extend('  ');i+=2;continue
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if string:
            if c=='\\' and i+1<len(text):
                out.extend('  ');i+=2;continue
            if c=='"': string=False
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if pair=='/-':
            depth=1;out.extend('  ');i+=2;continue
        if pair=='--':
            stop=text.find('\n',i)
            stop=len(text) if stop<0 else stop
            out.extend(' '*(stop-i));i=stop;continue
        if c=='"':
            string=True;out.append(' ');i+=1;continue
        out.append(c);i+=1
    if depth: raise ValueError('Unclosed Lean block comment')
    if string: raise ValueError('Unclosed Lean string literal')
    return ''.join(out)


def declarations(text):
    scopes=[]
    parts=[]
    result=[]
    seen=set()
    source = list(without_comments(text))
    # Attributes can share a line with an exported declaration. Mask their
    # balanced syntax while retaining line positions; Lean resolves the names.
    i = 0
    while i < len(source):
        if ''.join(source[i:i + 2]) != '@[':
            i += 1
            continue
        depth = 1
        source[i:i + 2] = [' ', ' ']
        i += 2
        while i < len(source) and depth:
            char = source[i]
            if char == '[':
                depth += 1
            elif char == ']':
                depth -= 1
            if char != '\n':
                source[i] = ' '
            i += 1
        if depth:
            raise ValueError('Unclosed Lean attribute')
    for line in ''.join(source).splitlines():
        line = line.lstrip()
        opened=re.match(r'^(namespace|(?:noncomputable )?section)\s*(\S+)?',line)
        if opened:
            kind,name=opened.groups()
            if kind=='namespace':
                if not name: raise ValueError('Namespace without a name')
                scopes.append(('namespace',name,len(parts)))
                parts.extend(name.split('.'))
            else:
                scopes.append(('section',name,len(parts)))
            continue
        closed=re.match(r'^end(?:\s+(\S+))?\s*$',line)
        if closed:
            name=closed.group(1)
            if scopes:
                if name and scopes[-1][1]!=name: raise ValueError('Unmatched named scope end '+name)
                kind,_,width=scopes.pop()
                if kind=='namespace': parts=parts[:width]
            elif name: raise ValueError('Named scope end without open scope '+name)
            continue
        declaration=re.match(r'^(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s({:\[]+)',line)
        if declaration:
            kind,name=declaration.groups()
            if not parts: raise ValueError('Declaration without a namespace '+name)
            full='.'.join(parts)+'.'+name
            if full in seen: raise ValueError('Duplicate local declaration '+full)
            seen.add(full)
            result.append(dict(name=full,kind=kind))
    if any(kind=='namespace' for kind,_,_ in scopes): raise ValueError('Unclosed named namespace')
    return result
