import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac

/-! Persistent Jacobian ECDH with signed five-bit windows and cached table powers. -/
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
namespace VG.Impl.Ecdh.X86_64.Window5

def fp (M : Mod) (ops : List FOp) : Prog isa := ForwardField.programB M ops
def dbl (K : WinCfg) (p o : Pt) : Prog isa :=
  .seq (.block (if p.x == o.x && p.y == o.y && p.z == o.z then [] else copyPt 4 o p))
    (VG.Impl.P256.X86_64.doubleHalfPublic K.M K.S o)

def mixed (K : WinCfg) (p q o : Pt) : Prog isa :=
  .seq (.block (copy 4 K.S.t2 p.x ++ copy 4 K.S.t4 p.y))
    (fp K.M (jacMixedHead K.S p q ++ jacMixedTail K.S p q o))

def select (K : WinCfg) : List Instr :=
  WinCfg.selSetup K ++
    (if K.M.adx then selPassY K.E.x 16 160 5 (2 * ·)
     else selPassAt K.E.x 16 160 10 (16 * ·)) ++ WinCfg.ySel0 K

def window (K : WinCfg) : Prog isa :=
  let h := 16
  let tablePt := fun m => Pt.mk (K.tbl+160*(m-1)) (K.tbl+160*(m-1)+32) (K.tbl+160*(m-1)+64)
  let tc := {WinCfg.tc K with w := 5, kbytes := 5*K.J}
  let tableLoad :=
    .seq (.block [.mov .rax (.reg .rbx),.alu .test .rbx (.imm 1)]) <|
    .seq (.ite .e (.block [.shift .shr .rax 1]) (.block [.alu .sub .rax (.imm 1)])) <|
    .block ([.alu .sub .rax (.imm 1),.mov32 .rcx (.imm 160),.mul .rcx,
      .mov .rdx (.reg .rdi),.alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl)),.alu .add .rdx (.reg .rax)] ++
      (List.range 6).flatMap (fun i => [.movdquLoad (selAcc i) (tblAt (16*i)),.movdquStore (sc (K.R.x+16*i)) (selAcc i)]))
  let tableStore :=
    [.mov .rax (.reg .rbx),.alu .sub .rax (.imm 1),.mov32 .rcx (.imm 160),.mul .rcx,
     .mov .rdx (.reg .rdi),.alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl)),.alu .add .rdx (.reg .rax)] ++
    (List.range 6).flatMap (fun i => [.movdquLoad (selAcc i) (sc (K.R.x+16*i)),.movdquStore (tblAt (16*i)) (selAcc i)])
    ++ (List.range 4).flatMap (fun i => [.movdquLoad (selAcc i) (sc (K.E.x+96+16*i)),.movdquStore (tblAt (96+16*i)) (selAcc i)])
  let build := .seq (.block (copyPt 4 (tablePt 1) K.P ++ setConst 4 ((tablePt 1).x+96) K.one ++ setConst 4 ((tablePt 1).x+128) K.one ++ [.mov32 .rbx (.imm 2)])) <|
    .loop (.seq tableLoad <|
      .seq (.block [.alu .test .rbx (.imm 1)]) <|
      .seq (.ite .e (dbl K K.R K.R)
        (.seq (mixed K K.R K.P K.D) (.block (copyPt 4 K.R K.D)))) <|
      .seq (fp K.M [.mul (K.E.x+96) K.R.z K.R.z,.mul (K.E.x+128) (K.E.x+96) K.R.z]) <|
      .block (tableStore ++ [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm (BitVec.ofNat 32 (h+1)))])) .ne
  let doubles := .seq (.block [.alu .add .rbx (.imm (BitVec.ofNat 32 20480))]) <|
    .loop (.seq (dbl K K.R K.R)
      (.block [.alu .sub .rbx (.imm 4096),.alu .cmp .rbx (.imm 4096)])) .ae
  let head := fp K.M (CachedJac.head K.S K.R K.E (K.E.x+96))
  let tail := jacTail K.S K.R K.E K.D
  let add := .seq head <| .seq (fp K.M tail) <|
    .block (nzMask 4 K.R.z ++ selPt 4 K.D K.E K.D ++
      nzMask 4 K.E.z ++ selPt 4 K.D K.R K.D ++ copyPt 4 K.R K.D)
  .seq build <|
  .seq (.block ([.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J-1)))] ++
    tc.digit ++ select K ++ tc.negY ++ copyPt 4 K.R K.E)) <|
  .seq (.loop (
    .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq doubles <|
    .seq (.block (tc.digit ++ select K ++ tc.negY)) <|
    .seq add (.block [.alu .test .rbx (.reg .rbx)])) .ne) <|
  fp K.M [.mul K.R.z K.R.z K.R.z]

def exchange (c : Ecdsa.X86_64.Cfg) : Prog isa :=
  let j := 52
  let offset := 16*((32^52-1)/31)
  let prep := .seq (.block (WinCfg.addConst 4 (c.sl K) c.winK offset))
    (bits c.winK c.winBits 40)
  let k := {c.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP with J := j, E := ⟨7360,7392,7424⟩}
  .seq (.block Impl.Ecdh.X86_64.Cfg.args) <| .seq (Impl.Ecdh.X86_64.Cfg.prefix' c none) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <| .seq (Impl.Ecdh.X86_64.Cfg.validate c) <|
  .seq prep <| .seq (window k) <|
  .seq c.pPow (Impl.Ecdh.X86_64.Cfg.middle c)

def exchangeP256 : Prog isa := exchange p256
def exchangeP256Adx : Prog isa := exchange p256x

end VG.Impl.Ecdh.X86_64.Window5
