module

import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindowCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindowCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponent
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSelect
import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindow
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Public exponentiation leaks only its public exponent and layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- Fixed public byte through its two windows. -/
def WinI (bd : Nat → Nat → Nat) (p : XPub × Nat) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc E : Nat),
    CWinInv t₀ (off p.1.B p.1.o) p.1.wx minv X Xc (bd X (2 ^ (64 * p.1.wx))) False 0 E p.2 j s ∧
    2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.1.wx)) X ∧ Xc < X ∧ p.2 < 256

theorem wins_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two fun p s => 0 < 2 ∧ WinI Sq.bd p 0 s) (.loop (seqs (window Sq.mm M.mm)) .ne)
      (Two fun p s => WinI Sq.bd p 2 s) := by
  apply two_loop (Φ := WinI Sq.bd) (fun _ => 2)
  · apply two_map (fun q : (XPub × Nat) × Nat => (q.1.1, q.1.2 * 16 ^ q.2)) ?_ (window_ct M Sq)
    intro q s ⟨hj, t₀, minv, X, Xc, E, hI, hw, hw', hR, _, hv⟩
    have hp : 16 ^ q.2 ≤ 16 := by rcases (show q.2 = 0 ∨ q.2 = 1 by omega) with h | h <;> rw [h] <;> decide
    exact ⟨minv, X, Xc, hI.ctx, hI.tab, hI.ylt, hI.v,
      by have := Nat.mul_le_mul_left q.1.2 hp; omega, hw, hw', hR⟩
  · intro p j s hj ⟨t₀, minv, X, Xc, E, hI, hw, hw', hR, hXN, hv⟩
    exact WP.mono (crtWinStep_ok M Sq hw hw' hR hv hj hI) fun _ ⟨hz, hI'⟩ =>
      ⟨eval_ne_count hj hz, fun _ => ⟨t₀, minv, X, Xc, E, hI', hw, hw', hR, hXN, hv⟩,
        fun h => h ▸ ⟨t₀, minv, X, Xc, E, hI', hw, hw', hR, hXN, hv⟩⟩

def CBytesInv (bd : Nat → Nat → Nat) (a : BPub × List Byte) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat),
    CByteInv t₀ (off a.1.x.B a.1.x.o) a.1.x.wx minv X Xc (bd X (2 ^ (64 * a.1.x.wx))) False 0 a.1.ptr a.2.length a.2 i s ∧ 2 ≤ a.1.x.wx ∧
    a.1.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * a.1.x.wx)) X ∧ Xc < X ∧
    a.2.length = a.1.len ∧ a.2.length < 2 ^ 31 ∧ Src t₀ a.1.x.B a.1.x.Z a.1.ptr a.2 ∧
    ∀ i < a.2.length, slot a.1.x.wx 8 + tabBytes a.1.x.wx ≤ ofs (off a.1.x.B a.1.x.o) (a.1.ptr + BitVec.ofNat 64 i)

/-- After the loads of the byte's address. -/
def CHeadMid (bd : Nat → Nat → Nat) (q : (BPub × List Byte) × Nat) (s : State) : Prop :=
  q.2 < q.1.1.len ∧ CBytesInv bd q.1 q.2 s ∧ s.gpr .rax = q.1.1.ptr ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

theorem pins_cBytes {bd : Nat → Nat → Nat} :
    Pins (fun (q : (BPub × List Byte) × Nat) s => q.2 < q.1.1.len ∧ CBytesInv bd q.1 q.2 s) [.rdi] :=
  pins_rdi (fun q : (BPub × List Byte) × Nat => off q.1.1.x.B q.1.1.x.o) fun _ _ ⟨_, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi

theorem pins_cHeadMid {bd : Nat → Nat → Nat} : Pins (CHeadMid bd) [.rdi, .rax, .rcx] := by
  rintro q s₁ s₂ ⟨-, ⟨_, _, _, _, i₁, _⟩, a₁, c₁⟩ ⟨-, ⟨_, _, _, _, i₂, _⟩, a₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of the exponent leaks the same in runs with the same workspace
and the same public exponent bytes, pointer and length. -/
theorem crtByte_ct (M : Mont) (Sq : MontS) : RelCT isa (Two fun (q : (BPub × List Byte) × Nat) s => q.2 < q.1.1.len ∧ CBytesInv Sq.bd q.1 q.2 s)
    (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (window Sq.mm M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) fun _ _ => True := by
  simp only [seqs]
  rw [crtByteHead_eq]
  have w₁ : ∀ (q : (BPub × List Byte) × Nat) s, q.2 < q.1.1.len ∧ CBytesInv Sq.bd q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) s (CHeadMid Sq.bd q) := by
    rintro q s ⟨hi, t₀, minv, X, Xc, hI, hrest⟩
    exact WP.mono (crtByteHead1_ok hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, minv, X, Xc, h3, hrest⟩, h1, h2⟩
  have w₂ : ∀ (q : (BPub × List Byte) × Nat) s, CHeadMid Sq.bd q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
        .mov32 .rax (.imm 2), .store (hdr Crt.sBit) .rax]) s fun t => 0 < 2 ∧ WinI Sq.bd (q.1.1.x, (q.1.2[q.2]?.getD 0).toNat) 0 t := by
    rintro q s ⟨hi, ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN, hL, -, he, hout⟩, hax, hcx⟩
    have hi' : q.2 < q.1.2.length := by omega_arith
    exact WP.mono (crtByteHead2_ok rfl hi' he.rd he.val hout hI hax hcx) fun t ⟨_, _, hB⟩ =>
      ⟨by decide, t, minv, X, Xc, _, by simpa only [List.getElem?_eq_getElem hi', Option.getD_some] using hB, hw, hw', hR, hXN, (q.1.2[q.2]?.getD 0).isLt⟩
  have h₃ : RelCT isa (Two fun (p : XPub × Nat) s => WinI Sq.bd p 2 s)
      (.block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]) fun _ _ => True :=
    rdi_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq (two_piece _ pins_cBytes (by taint_decide) w₁)
      (two_piece _ pins_cHeadMid (by taint_decide) w₂)))
    (RelCT.seq (two_map (fun q : (BPub × List Byte) × Nat => (q.1.1.x, (q.1.2[q.2]?.getD 0).toNat)) (fun _ _ h => h) (wins_ct M Sq)) h₃)

def EPre (sp sl : Nat) (p : BPub × List Byte) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X x y : Nat),
    SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx minv ∧ 2 ≤ p.1.x.wx ∧ p.1.x.wx ≤ p.1.x.w ∧ p.1.x.w < 2 ^ 30 ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aN) p.1.x.wx = X ∧
    ((word s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
    X % 2 = 1 ∧ wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Crt.aXc) p.1.x.wx < X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Crt.aXc) p.1.x.wx % X = x * 2 ^ (64 * p.1.x.wx) % X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aY) p.1.x.wx < X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aY) p.1.x.wx % X = y * 2 ^ (64 * p.1.x.wx) % X ∧
    sp < 32 ∧ sl < 32 ∧ word s.mem p.1.x.B (8 * sp) = p.1.ptr ∧
    word s.mem p.1.x.B (8 * sl) = BitVec.ofNat 64 p.2.length ∧ p.2.length = p.1.len ∧ 1 ≤ p.2.length ∧
    p.2.length ≤ 1024 ∧ Src s p.1.x.B p.1.x.Z p.1.ptr p.2


theorem EPre.secret {sp sl : Nat} {p : BPub × List Byte} {s : State} (h : EPre sp sl p s) :
    VG.Proof.Bignum.X86_64.EPre sp sl p.1 s := by
  obtain ⟨minv, X, x, y, hrest⟩ := h
  exact ⟨minv, X, x, y, p.2, hrest⟩

theorem crtExpLoop_ct (M : Mont) (Sq : MontS) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc).isSome = true) :
    RelCT isa (Two (EPre sp sl)) (VG.Impl.Dsa.X86_64.PublicPower.expLoop Sq.mm M.mm sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.expLoop
  refine RelCT.seq (two_post
    (Ψ := fun a s => 0 < a.1.len ∧ CBytesInv Sq.bd a 0 s) ?_ fun a s h => ?_) ?_
  · -- The start and the table.
    rw [← List.singleton_append]
    refine RelCT.seqs_append (by simp) (by simp [Crt.tabBuild, tabBuild_eq, tabPre]) (RelCT.seq (two_post (Ψ := fun a s => TPre 16 a.1.x s)
      ?_ fun _ _ h => by exact crtExpInit_tpre h.secret) (two_map (fun a : BPub × List Byte => a.1.x)
        (fun _ _ h => h) (tabBuild_ct M 16 (by decide) (by decide) (by taint_decide))))
    rw [crtExpInit_eq]
    exact RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : BPub × List Byte) t => t.gpr .rdi = off a.1.x.B a.1.x.o ∧
        t.gpr .rax = a.1.x.B) [.rdi] ((pins_rdi (fun a : BPub × List Byte => off a.1.x.B a.1.x.o) (fun _ _ h => by
        obtain ⟨_, _, _, _, hc, _⟩ := h; exact hc.rdi))) (by taint_decide) fun _ _ h => crtLink_ok h.secret)
      (two_taint [.rdi, .rax] (pins_of (fun a r => if r = .rdi then off a.1.x.B a.1.x.o else a.1.x.B)
        fun a s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) hT))
  · obtain ⟨minv, X, x, y, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, hL, hL1, hL2,
      he⟩ := h
    have hPn := hc.scrT.nowrap
    have hBn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have h256 : 256 ≤ slot a.1.x.wx 8 := by unfold slot hdrBytes; omega_arith
    have hout : ∀ i < a.2.length, slot a.1.x.wx 8 + tabBytes a.1.x.wx ≤ ofs (off a.1.x.B a.1.x.o) (a.1.ptr + BitVec.ofNat 64 i) :=
      fun i hi' => by
        have := he.out i hi'
        rcases ofs_rebase a.1.x.B (a.1.ptr + BitVec.ofNat 64 i) (o := a.1.x.o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
        · omega_arith
        · omega_arith
    exact WP.mono (crtExpHead_ok M (Q := False) (x := 0) hc hw2 hwx hw30 hn hinv hodd hxl False.elim hyl False.elim
      hsp hsl hep hel he) fun t hI => ⟨by omega_arith, s, minv, X, _,
        CByteInv.mk hI.ctx hI.tab (Nat.lt_of_lt_of_le hI.ylt
          (Sq.le (by rw [← hn]; exact Nat.le_of_lt (wv_lt _ _ _ _)))) hI.y hI.idx hI.e hI.len hI.frm hI.keep,
        hw2, by omega_arith,
        VG.Proof.Bignum.coprime_pow2 hodd _, hxl, hL, by omega_arith, he, hout⟩
  unfold VG.Impl.Dsa.X86_64.PublicPower.byte
  refine (two_loop (Φ := CBytesInv Sq.bd) (Ψ := fun _ _ => True) (fun a => a.1.len) (crtByte_ct M Sq) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rintro a i s hi ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN, hL, hL', he, hout⟩
  exact WP.mono (crtByte_ok M Sq hw hw' hR rfl hL' (by omega_arith) he.rd he.val hout hI)
    fun s' ⟨hz, hI'⟩ => ⟨eval_ne_count hi (by rw [hz, hL]), fun _ => ⟨t₀, minv, X, Xc, hI', hw, hw', hR, hXN, hL,
      hL', he, hout⟩, fun _ => trivial⟩


end VG.Proof.Dsa.X86_64.PublicPower
