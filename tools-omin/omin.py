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
errs=re.findall(r'^\S+?:(\d+):(\d+): error.*',o,re.M)
if errs: print("ERRORS:",o[:3000]); sys.exit(1)
res={}
for m in re.finditer(r'OMIN(-KEEP)?@(\d+):(\d+) (.*)$',o,re.M):
    res[(int(m.group(2))-1,int(m.group(3)))]=(m.group(1),m.group(4))
# build output on ORIGINAL text
ol=text.split("\n"); n_rep=n_keep=0; sizes=[]
inv={}
for orig in range(lo,min(hi,len(lines))+1):
    ln=newline(orig)-1
    for m in re.finditer(r'\bomega_arith\b(?!_)',lines[orig-1]): inv.setdefault(orig-1,[]).append(m.start())
# map: occurrences in new text (after replacement columns are same start)
for oi,cols in inv.items():
    ln=newline(oi+1)-1
    order=sorted(cols)
    for c in sorted(cols,reverse=True):
        r_=res.get((ln,c-2*order.index(c)))
        if r_ is None: print("no result for",oi+1,c); continue
        keep,arg=r_
        if keep: n_keep+=1; continue
        ol[oi]=ol[oi][:c]+"omega_using "+arg+ol[oi][c+len("omega_arith"):]; n_rep+=1; sizes.append(arg.count(",")+1 if arg!="[]" else 0)
open(out,"w").write("\n".join(ol))
print(f"replaced {n_rep}, kept {n_keep}; facts per call: {sizes}")
