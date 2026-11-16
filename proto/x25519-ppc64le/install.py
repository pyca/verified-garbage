# Replaces the body of the generated vg_x25519 with a prototype's text. Measurement only.
import subprocess,sys
f="crates/verified-garbage-asm-powerpc64le/src/internal/vg_x25519.rs"
src=subprocess.run(["git","show","origin/main:"+f],capture_output=True,text=True,check=True).stdout.split("\n")
asm=subprocess.run(["python3"]+sys.argv[1:],capture_output=True,text=True,check=True).stdout
open(f,"w").write("\n".join(src[:13])+'\n        r#"\n'+asm+'\n"#,\n    )\n}\n')
