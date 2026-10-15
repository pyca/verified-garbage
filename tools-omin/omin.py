#!/usr/bin/env python3
"""omin.py <module file> <out file> [first_line last_line]: replace omega_arith by the minimal omega_using [..]."""
import re,sys,subprocess,os
src,out=sys.argv[1],sys.argv[2]
lo,hi=(int(sys.argv[3]),int(sys.argv[4])) if len(sys.argv)>4 else (1,10**9)
S="/tmp/claude-0/-home-user-verified-garbage/fff7281b-06d2-5b97-bf74-c88816cc428b/scratchpad"
lean_dir="/home/user/verified-garbage/lean"
env=dict(os.environ); env["PATH"]=os.path.expanduser("~/.elan/bin")+":"+env["PATH"]
key=src.replace('/','_').replace('.','_'); setup=f"{lean_dir}/.lake/setup_{key}.json"
if not os.path.exists(setup):
    open(setup,"w").write(subprocess.run(["lake","setup-file","--log-level=warning",src],cwd=lean_dir,env=env,capture_output=True,text=True).stdout)
text=open(os.path.join(lean_dir,src)).read()
lines=text.split("\n")
# insert header after the last import line
last_imp=max(i for i,l in enumerate(lines) if re.match(r'^(public |meta |private )*import ',l))
hdr=open(S+"/omin_header.lean").read().rstrip("\n").split("\n")
# imports must precede other content: split header into imports + rest
himp=[l for l in hdr if l.startswith("public meta import")]; hrest=[l for l in hdr if not l.startswith("public meta import")]
# put rest right before first "@[expose] public section" or namespace
first_sec=next(i for i,l in enumerate(lines) if l.startswith("@[expose]") or l.startswith("namespace"))
off_lines=len(himp)+len(hrest)
new=lines[:last_imp+1]+himp+lines[last_imp+1:first_sec]+hrest+lines[first_sec:]
shift_after_imp=len(himp); shift_after_sec=len(himp)+len(hrest)
def newline(orig):  # orig 1-based
    i=orig-1
    return orig+(shift_after_sec if i>=first_sec else shift_after_imp if i>last_imp else 0)
t="\n".join(new)
# replace omega_arith in range (original line numbers) with omega_min, track positions
occ=[]
tl=t.split("\n")
for orig in range(lo,min(hi,len(lines))+1):
    ln=newline(orig)-1
    if ln>=len(tl): break
    for m in re.finditer(r'\bomega_arith\b(?!_)',tl[ln]): occ.append((ln,m.start()))
for ln,c in sorted(occ,reverse=True):
    tl[ln]=tl[ln][:c]+"omega_min"+tl[ln][c+len("omega_arith"):]
open(out+".min.lean","w").write("\n".join(tl))
r=subprocess.run(["lake","env","lean","--setup",setup,out+".min.lean"],cwd=lean_dir,env=env,capture_output=True,text=True)
o=r.stdout+r.stderr
errs=[e for e in re.findall(r'^\S+?:(\d+):(\d+): error(.*)',o,re.M) if 'is not explicitly referenced' not in e[2]]
if errs: print("ERRORS:",o[:3000]); sys.exit(1)
res={}
for m in re.finditer(r'OMIN(-KEEP)?@(\d+):(\d+) (.*)$',o,re.M):
    k=(int(m.group(2))-1,int(m.group(3)))
    keep,arg=m.group(1),m.group(4)
    if k in res:
        pk,pa=res[k]
        if pk or keep: res[k]=("-KEEP",""); continue
        names=[x for x in pa.strip("[]").split(", ") if x]
        for x in arg.strip("[]").split(", "):
            if x and x not in names: names.append(x)
        res[k]=(None,"["+", ".join(names)+"]")
    else: res[k]=(keep,arg)
# sites on ORIGINAL text: (line index, col, replacement)
sites=[]
for orig in range(lo,min(hi,len(lines))+1):
    oi=orig-1; ln=newline(orig)-1
    cols=[m.start() for m in re.finditer(r'\bomega_arith\b(?!_)',lines[oi])]
    for k,c in enumerate(cols):
        r_=res.get((ln,c-2*k))
        if r_ is None or r_[0]: continue
        sites.append((oi,c,"omega_using "+r_[1]))
decl_starts=[i for i,l in enumerate(lines) if re.match(r'^(@\[[^\]]*\]\s*)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure)\b',l)]
def decl_range(li):
    s=max([d for d in decl_starts if d<=li],default=0); e=min([d for d in decl_starts if d>li],default=len(lines))
    return s,e
active=set(range(len(sites)))
def render():
    ol=list(lines); pos={}
    by_line={}
    for i in active: by_line.setdefault(sites[i][0],[]).append(i)
    for li,ids in by_line.items():
        ids.sort(key=lambda i:sites[i][1],reverse=True)
        for i in ids:
            _,c,rep=sites[i]; ol[li]=ol[li][:c]+rep+ol[li][c+len("omega_arith"):]
        # positions after rewrite: recompute columns left-to-right
        shift=0
        for i in sorted(ids,key=lambda i:sites[i][1]):
            pos[(li+1,sites[i][1]+shift)]=i; shift+=len(sites[i][2])-len("omega_arith")
    return "\n".join(ol),pos
for it in range(8):
    txt,pos=render(); open(out,"w").write(txt)
    r=subprocess.run(["lake","env","lean","--setup",setup,out],cwd=lean_dir,env=env,capture_output=True,text=True)
    errs=re.findall(r'^\S+?:(\d+):(\d+): error(.*)',r.stdout+r.stderr,re.M)
    if not errs: break
    bad=set()
    for l,c,msg in errs:
        l,c=int(l),int(c)
        if (l,c) in pos: bad.add(pos[(l,c)]); continue
        s,e=decl_range(l-1)
        bad|={i for i in active if s<=sites[i][0]<e}
    if not bad & active: print("UNRESOLVED", errs[:3]); sys.exit(1)
    active-=bad
sizes=[sites[i][2].count(",")+1 if not sites[i][2].endswith("[]") else 0 for i in sorted(active)]
print(f"replaced {len(active)} of {sum(len(re.findall(r'\bomega_arith\b(?!_)',lines[i-1])) for i in range(lo,min(hi,len(lines))+1))}; reverted {len(sites)-len(active)}; facts per call: {sizes}")
