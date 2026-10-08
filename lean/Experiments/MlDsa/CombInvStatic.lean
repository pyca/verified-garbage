import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith
open VG.Impl.MlKem.AArch64 (mov)
namespace CombInvImmediate
def vr : Nat → VReg | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7
def z (i : Nat) : Nat := (8380417-1753^Spec.MlDsa.bitRev8 i%8380417)%8380417
def bar (x : Nat) : Nat := x*2149582593/2^23
def setup : Prog isa := .block <| (List.range 256).flatMap fun j =>
 movW .x9 (z (255-j)) ++ [.str .w .x9 .x1 (4*j)] ++
 movW .x9 (bar (z (255-j))) ++ [.str .w .x9 .x1 (1024+4*j)]
def cv (r : VReg) (xs : List Nat) : List Instr :=
 movW .x9 xs[0]! ++ [.vop (.dup .s4 r .x9)] ++
 (List.range 3).flatMap (fun j => if xs[j+1]! = xs[0]! then [] else movW .x9 xs[j+1]! ++ [.vop (.ins .s4 r (j+1) .x9)])
def root (idx len : Nat) : List Instr :=
 let off := 4*(255-idx)
 if len=1 then [.ldrq .v20 .x1 off,.ldrq .v21 .x1 (1024+off)]
 else if len=2 then [.ldr .x .x9 .x1 off,.ldr .x .x10 .x1 (1024+off),
 .vop (.dup .d2 .v20 .x9),.vop (.dup .d2 .v21 .x10),
 .vop (.perm .zip1 .s4 .v20 .v20 .v20),.vop (.perm .zip1 .s4 .v21 .v21 .v21)]
 else [.ldr .w .x9 .x1 off,.ldr .w .x10 .x1 (1024+off),.vop (.dup .s4 .v20 .x9),.vop (.dup .s4 .v21 .x10)]
def mul (d : VReg) : List Instr :=
 [.vop (.sqdmulh .v19 d .v21),.vop (.mul d d .v20),.vop (.mls d .v19 .v31)]
def butterfly (a b : VReg) : List Instr :=
 [.vop (.sub .s4 .v18 a b),.vop (.add .s4 a a b),.vop (.mov b .v18)] ++ mul b
def packed (a b : VReg) (len : Nat) : List Instr :=
 let perm := if len=1 then VPermOp.uzp1 else .trn1
 let perm2 := if len=1 then VPermOp.uzp2 else .trn2
 let shape := if len=1 then VArr.s4 else .d2
 [.vop (.perm perm shape .v16 a b),.vop (.perm perm2 shape .v17 a b)] ++ [.vop (.sub .s4 .v18 .v16 .v17),.vop (.add .s4 .v16 .v16 .v17)] ++ mul .v18 ++
 (if len=1 then [.vop (.perm .zip1 .s4 a .v16 .v18),.vop (.perm .zip2 .s4 b .v16 .v18)]
 else [.vop (.perm .trn1 .d2 a .v16 .v18),.vop (.perm .trn2 .d2 b .v16 .v18)])
structure CS where
 code : List Instr := []
 regs : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7]
 free : List VReg := [.v24,.v25,.v26,.v27]
def qt : Nat → VReg | 0 => .v16 | 1 => .v17 | 2 => .v18 | _ => .v19
def batch (st : CS) (pairs : List (Nat × Nat)) : CS :=
 let ds := (List.range pairs.length).flatMap fun j =>
  let (ai,bi) := pairs[j]!
  [.vop (.sub .s4 st.free[j]! st.regs[ai]! st.regs[bi]!),.vop (.add .s4 st.regs[ai]! st.regs[ai]! st.regs[bi]!)]
 let qs := (List.range pairs.length).map fun j => Instr.vop (.sqdmulh (qt j) st.free[j]! .v21)
 let ms := (List.range pairs.length).map fun j => Instr.vop (.mul st.free[j]! st.free[j]! .v20)
 let rs := (List.range pairs.length).map fun j => Instr.vop (.mls st.free[j]! (qt j) .v31)
 let regs := (List.range pairs.length).foldl (fun r j => r.set pairs[j]!.2 st.free[j]!) st.regs
 let free := (List.range pairs.length).foldl (fun r j => r.set j st.regs[pairs[j]!.2]!) st.free
 ⟨st.code++ds++qs++ms++rs,regs,free⟩
def firstBlock (base : Nat) : List Instr :=
 let ld := (List.range 8).map (fun j => Instr.ldrq (vr j) .x0 (4*base+16*j))
 let packedCode := [1,2].flatMap (fun len => (List.range 4).flatMap (fun j => root (256/len-1-(base+8*j)/(2*len)) len ++ packed (vr (2*j)) (vr (2*j+1)) len))
 let st : CS := {code := ld++packedCode}
 let st := [4,8,16].foldl (fun st len => (List.range (16/len)).foldl (fun st b =>
   batch {st with code := st.code++root (256/len-1-base/(2*len)-b) len}
    ((List.range (len/4)).map (fun j => (b*len/2+j,b*len/2+j+len/4)))) st) st
 st.code ++ (List.range 8).map (fun j => Instr.strq st.regs[j]! .x0 (4*base+16*j))
def canon (d : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 .v19 d 31),.vop (.logic .and .v19 .v19 .v31),.vop (.add .s4 d d .v19),
 .vop (.sub .s4 .v19 d .v31),.vop (.umin d d .v19)]
def finalBody : List Instr :=
 let st : CS := {code := (List.range 8).map (fun j => Instr.ldrq (vr j) .x2 (128*j))}
 let st := [1,2,4].foldl (fun st dist => (List.range (4/dist)).foldl (fun st b =>
   batch {st with code := st.code++root (8/dist-1-b) 4}
    ((List.range dist).map (fun j => (2*b*dist+j,2*b*dist+j+dist)))) st) st
 st.code ++ movW .x9 16382 ++ movW .x10 (bar 16382) ++ [.vop (.dup .s4 .v20 .x9),.vop (.dup .s4 .v21 .x10)] ++
 (List.range 8).flatMap (fun j => mul st.regs[j]! ++ canon st.regs[j]! ++ [.strq st.regs[j]! .x2 (128*j)]) ++
 [.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]
def core : Prog isa :=
 .seq (.block (movW .x9 8380417 ++ [.vop (.dup .s4 .v31 .x9)] ++ (List.range 8).flatMap (fun j => firstBlock (32*j)) ++ [mov .x2 .x0,.movz .x .x12 8 0]))
 (.loop (.block finalBody) (.nonzero .x .x12))
end CombInvImmediate


def staticCode : Prog isa := .seq (.block [.adrSym .x1 "VG_MLDSA_INV_ZETAS"]) CombInvImmediate.core
def tableWords : List (BitVec 64) :=
 let xs := (List.range 256).map (fun j => CombInvImmediate.z (255-j))
 let vals := xs ++ xs.map CombInvImmediate.bar
 (List.range 256).map (fun j => BitVec.ofNat 64 (vals[2*j]!+2^32*vals[2*j+1]!))
def main : IO Unit := do
 let ls := printer.function staticCode
 IO.FS.writeFile "/tmp/comb-inv-static.body" (String.join (ls.map (Rust.line printer.call)))
 IO.FS.writeFile "/tmp/comb-inv-static-consts.rs" ("// EXPERIMENTAL, UNPROVED. Exact Lean table data.\n" ++ Rust.tablesFile "aarch64" [("VG_MLDSA_INV_ZETAS",tableWords)])
 IO.FS.writeFile "/tmp/comb-inv-static.bindings" "        VG_MLDSA_INV_ZETAS = sym super::consts::VG_MLDSA_INV_ZETAS,\n"
 IO.FS.writeFile "/tmp/comb-inv-static-table.h" ("__attribute__((aligned(64))) const uint64_t VG_MLDSA_INV_ZETAS[256] = {\n" ++ String.intercalate ",\n" (tableWords.map (fun w => toString w.toNat ++ "ULL")) ++ "\n};\n")
 IO.println s!"static inverse: {ls.length} lines, {tableWords.length*8} table bytes"
