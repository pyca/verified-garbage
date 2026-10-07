import VerifiedGarbage.Impl.Ecdh.P256.X86_64
import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJacMasked

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

def tablePt (K : WinCfg) (m : Nat) : Pt :=
  ⟨K.tbl+160*(m-1),K.tbl+160*(m-1)+32,K.tbl+160*(m-1)+64⟩

def tableAddress (tbl : Nat) : List Instr :=
  [.alu .sub .rax (.imm 1),.mov32 .rcx (.imm 160),.mul .rcx,
   .mov .rdx (.reg .rdi),.alu .add .rdx (.imm (BitVec.ofNat 32 tbl)),.alu .add .rdx (.reg .rax)]

def tableLoad (K : WinCfg) : Prog isa :=
  .seq (.block [.mov .rax (.reg .rbx),.alu .test .rbx (.imm 1)]) <|
  .seq (.ite .e (.block [.shift .shr .rax 1]) (.block [.alu .sub .rax (.imm 1)])) <|
  .block (tableAddress K.tbl ++
    (List.range 6).flatMap (fun i => [.movdquLoad (selAcc i) (tblAt (16*i)),.movdquStore (sc (K.R.x+16*i)) (selAcc i)]))

def tableStore (K : WinCfg) : List Instr :=
  ([.mov .rax (.reg .rbx)] : List Instr) ++ tableAddress K.tbl ++
  (List.range 6).flatMap (fun i => [.movdquLoad (selAcc i) (sc (K.R.x+16*i)),.movdquStore (tblAt (16*i)) (selAcc i)])
  ++ (List.range 4).flatMap (fun i => [.movdquLoad (selAcc i) (sc (K.E.x+96+16*i)),.movdquStore (tblAt (96+16*i)) (selAcc i)])

def cache (K : WinCfg) : Prog isa :=
  fp K.M [.mul (K.E.x+96) K.R.z K.R.z,.mul (K.E.x+128) (K.E.x+96) K.R.z]

def tableCalc (K : WinCfg) : Prog isa :=
  .ite .e (dbl K K.R K.R)
    (.seq (mixed K K.R K.P K.D) (.block (copyPt 4 K.R K.D)))

def tableStep (K : WinCfg) : Prog isa :=
  .seq (tableLoad K) <|
  .seq (.block [.alu .test .rbx (.imm 1)]) <|
  .seq (tableCalc K) <|
  .seq (cache K) <|
  .block (tableStore K ++ [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 17)])

def build (K : WinCfg) : Prog isa :=
  .seq (.block (copyPt 4 (tablePt K 1) K.P ++ setConst 4 ((tablePt K 1).x+96) K.one ++ setConst 4 ((tablePt K 1).x+128) K.one ++ [.mov32 .rbx (.imm 2)]))
    (.loop (tableStep K) .ne)

def doubles (K : WinCfg) : Prog isa :=
  .seq (.block [.alu .add .rbx (.imm (BitVec.ofNat 32 20480))]) <|
  .loop (.seq (dbl K K.R K.R)
    (.block [.alu .sub .rbx (.imm 4096),.alu .cmp .rbx (.imm 4096)])) .ae

def add (K : WinCfg) : Prog isa :=
  .seq (CachedJac.maskedAdd K K.R K.E K.D (K.E.x+96)) (.block (copyPt 4 K.R K.D))

def window (K : WinCfg) : Prog isa :=
  let tc := {WinCfg.tc K with w := 5, kbytes := 5*K.J}
  .seq (build K) <|
  .seq (.block ([.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J-1)))] ++
    tc.digit ++ select K ++ tc.negY ++ copyPt 4 K.R K.E)) <|
  .seq (.loop (
    .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq (doubles K) <|
    .seq (.block (tc.digit ++ select K ++ tc.negY)) <|
    .seq (add K) (.block [.alu .test .rbx (.reg .rbx)])) .ne) <|
  fp K.M [.mul K.R.z K.R.z K.R.z]

def cfg (c : Ecdsa.X86_64.Cfg) : WinCfg :=
  {c.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP with
    J := 52, E := ⟨7360,7392,7424⟩}

def exchange (c : Ecdsa.X86_64.Cfg) : Prog isa :=
  let offset := 16*((32^52-1)/31)
  let prep := .seq (.block (WinCfg.addConst 4 (c.sl K) c.winK offset))
    (bits c.winK c.winBits 40)
  let k := cfg c
  .seq (.block Impl.Ecdh.X86_64.Cfg.args) <| .seq (Impl.Ecdh.X86_64.Cfg.prefix' c none) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <| .seq (Impl.Ecdh.X86_64.Cfg.validate c) <|
  .seq prep <| .seq (window k) <|
  .seq c.pPow (Impl.Ecdh.X86_64.Cfg.middle c)

def exchangeP256 : Prog isa := exchange p256
def exchangeP256Adx : Prog isa := exchange p256x

end VG.Impl.Ecdh.X86_64.Window5
