import sys,re
items=open('/tmp/gen.txt').read().strip().split(', ')
doc,name,guard,path=sys.argv[1:5]
out=f'/-- {doc} -/\ndef {name} : List Instr := [\n';line='  '
for i,it in enumerate(items):
    it+=',' if i<len(items)-1 else ']'
    if len(line)+len(it)>96: out+=line.rstrip()+'\n';line='  '
    line+=it+' '
out+=line.rstrip()+f'\n\n#guard {name} == {guard}'
s=open(path).read()
s=re.sub(r'--SBOX(?=\n)',lambda m:out,s,count=1)
open(path,'w').write(s)
