module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Setup
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Window
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.MillerRabin.Word32
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The IFMA Miller–Rabin round: correctness

`ifma_ok`: the round of a layout, in its frame: the setup, the vector code
(the table and the windows) under Intel's MXCSR prologue and epilogue, and
the flag; `code_correct`: the dispatch on the candidate's size, `round mul`
for the other sizes.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum (off word ofs Outside mask Frm wv)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52 at_)
open VG.Impl.Rsa.X86_64.PubIfma (arr)
open VG.Impl.MillerRabin.X86_64.Ifma
open VG.Impl.RsaKeyGen.X86_64.Candidate (aE aT0)
open VG.Proof.RsaKeyGen (mrA mrE wEnd)
open VG.Proof.MillerRabin.WindowK (kRun)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## The MXCSR prologue and epilogue -/

/-- `withMx`'s shape, from the prologue's and the epilogue's blocks whole. -/
theorem wp_mx {S P L R V : List Instr} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.block (S ++ P)) s fun s₁ => WP isa c s₁ fun s₂ => WP isa (.block (L ++ R ++ V)) s₂ Q) :
    WP isa (.seq (.seq (.block S) (.seq (.seq (.block P) (.seq c (.block L))) (.block R))) (.block V)) s Q := by
  refine WP.seq (WP.seq (WP.mono (WP.block_append_iff.mp h) fun s₁ h₁ => WP.seq (WP.seq (WP.mono h₁
    fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ h₃ => ?_)))))
  rw [List.append_assoc] at h₃
  exact WP.mono (WP.block_append_iff.mp h₃) fun s₄ h₄ => WP.block_append_iff.mp h₄

/-- The prologue: the caller's MXCSR, bits 31:16 cleared, in `rbp`, and
`MXCSR := 0x1FBF`. -/
theorem pro_ok {s : State} {B : Addr} {d Z : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B Z) (hd : d + 8 ≤ Z) :
    WP isa (.block [.stmxcsr (at_ .rbx d), .mov32 .rbp (.mem (at_ .rbx d)), .alu32 .and .rbp (.imm 0xFFFF),
        .mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (d + 4)) .rax, .ldmxcsr (at_ .rbx (d + 4)), .lfence]) s
      fun s' => s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧
        s'.gpr .rbp = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ Keep [.rbp, .rax] s s' := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  have hst4 : InRegions s.wr (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld4 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rbp, .rax] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧
      s'.gpr .rbp = (s.mxcsr &&& 0xFFFF).setWidth 64) (by
    xrun [ea_at'', hB, hst, hld, hst4, hld4, Mem.readW_writeW_self32]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- The epilogue: the saved MXCSR back from `rbp`. -/
theorem epi_ok {s : State} {B : Addr} {d Z : Nat} {v : BitVec 32} (hB : s.gpr .rbx = B) (hs : Scr s B Z)
    (hd : d + 8 ≤ Z) (hbp : s.gpr .rbp = (v &&& 0xFFFF).setWidth 64) :
    WP isa (.block ([.lfence] ++ [.store32 (at_ .rbx d) .rbp, .ldmxcsr (at_ .rbx d)] ++ [.vop .vzeroupper])) s
      fun s' => s'.mem = s.mem.writeW (off B d) (v &&& 0xFFFF) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  simp only [List.cons_append, List.nil_append]
  xrun [ea_at'', hB, hst, hld, hbp, Mem.readW_writeW_self32, VG.Proof.Bignum.X86_64.AmmSym.and_ffff_hi]
  and_intros <;> rfl

/-! ## The flag and the callee-saved registers -/

theorem ea_rsp (t : State) (d : Int) : t.ea { base := .rsp, disp := d } = t.gpr .rsp + BitVec.ofInt 64 d :=
  rfl

theorem finish_ok {u : State} {B S : Addr} (hB : u.gpr .rbx = B) (hS : u.gpr .rsp = S)
    (hF : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (oF l)) 8)
    (h0 : InRegions (u.rd ++ u.wr) S 8) (h8 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 8) 8)
    (h16 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 16) 8)
    (h24 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 24) 8)
    (h32 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 32) 8)
    (h40 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 40) 8) :
    WP isa (.block (finish l)) u fun t => t.gpr .rax = word u.mem B (oF l) &&& 1 ∧
      t.gpr .r15 = u.mem.readW S 64 ∧ t.gpr .r14 = u.mem.readW (S + 8#64) 64 ∧
      t.gpr .r13 = u.mem.readW (S + 16#64) 64 ∧ t.gpr .r12 = u.mem.readW (S + 24#64) 64 ∧
      t.gpr .rbp = u.mem.readW (S + 32#64) 64 ∧ t.gpr .rbx = u.mem.readW (S + 40#64) 64 ∧ t.mem = u.mem ∧
      Keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] u t := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun t =>
    t.gpr .rax = word u.mem B (oF l) &&& 1 ∧
      t.gpr .r15 = u.mem.readW S 64 ∧ t.gpr .r14 = u.mem.readW (S + 8#64) 64 ∧
      t.gpr .r13 = u.mem.readW (S + 16#64) 64 ∧ t.gpr .r12 = u.mem.readW (S + 24#64) 64 ∧
      t.gpr .rbp = u.mem.readW (S + 32#64) 64 ∧ t.gpr .rbx = u.mem.readW (S + 40#64) 64 ∧ t.mem = u.mem) (by
    unfold finish
    xrun [ea_at'', ea_rsp, BitVec.ofInt_ofNat, hB, hS, hF, h0, h8, h16, h24, h32, h40]) rfl)
    fun t ⟨⟨a, b, c, d, e, f, g, m⟩, k⟩ => ⟨a, b, c, d, e, f, g, m, k⟩

end VG.Proof.MillerRabin.X86_64.Ifma
