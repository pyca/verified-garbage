module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcCorrect
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scalar
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scan
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCorrect
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcCorrect
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scalar
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Scan
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_generate_key_precompute` on PPC64LE: constant time

Everything the precomputation computes is public: its addresses, counts and
branches are functions of the domain, its length, `p_len`, the context's,
the working space's and the table's addresses. The stages of `pc_correct`
fix the registers each piece reads; `main` runs as nine pieces (`mainG`), each
checked by the taint analysis from the registers that the one before fixes
(`main_pins`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Precompute
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)
open VG.Proof.Ffdh.PPC64LE.GenerateKey (bptr boundPtr_ok scan_ok scanRegs bptr_bnd)
open VG.Impl.Ffdh.PPC64LE.VettedValidation (tableSym tableConsts)
open VG.Spec.RsaKeyGen (bitLength)

/-! ## `main`, in pieces -/

/-- `boundBits` up to the bit loop. -/
def bbA : Prog isa :=
  .seq VG.Impl.Ffdh.PPC64LE.GenerateKey.boundPtr (.seq (.block VG.Impl.Ffdh.PPC64LE.GenerateKey.scanSetup)
    (.seq (VG.Impl.Bignum.PPC64LE.Precompute.countLoop .r6 VG.Impl.Ffdh.PPC64LE.GenerateKey.scanBody)
      (.block [.li .r15 0])))

/-- The bit loop and the bound's bit length. -/
def bbX : Prog isa :=
  .seq (.loop (.block [.lsr .d .r14 .r14 1, .addi .r15 .r15 1]) (.nonzero .d .r14))
    (.block [.sub .r16 .r28 .r22, .lsl .r16 .r16 3, .subi .r16 .r16 8, .add .r16 .r16 .r15])

def w1 : List Instr := [ldh .r8 hCap, .sub .r9 .r8 .r16, .lsr .d .r9 .r9 63]

def iteW : Prog isa := .ite (.zero .d .r8) (.block []) (.ite (.zero .d .r9) (.block []) (.block [.addi .r16 .r8 0]))

def m1 : List Instr := [.addi .r17 .r16 7, .lsr .d .r17 .r17 3]

def mrest : List Instr := [.store .d .r16 .r30 0, .store .d .r17 .r30 8, .store .d .r18 .r30 16, .addi .r24 .r18 0]

def tail : Prog isa := .seq montgomery (.seq storePrefix (.seq table (.block [.li .r3 1])))

/-- `main`, in the pieces the constant-time proof checks. -/
def mainG : Prog isa :=
  .seq bbA (.seq bbX (.seq (.block w1) (.seq iteW (.seq (.block m1) (.seq rows
    (.seq (.block [ldh .r30 hCtx]) (.seq (.block mrest) tail)))))))

theorem exec_block_split {l₁ l₂ : List Instr} {s t : State} {tr : List Leak}
    (e : Exec isa (.block (l₁ ++ l₂)) s tr t) : Exec isa (.seq (.block l₁) (.block l₂)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at e
  obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨⟨b, w⟩, hc, he⟩ := Option.map_eq_some_iff.mp hb
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact .seq (.block ha) (.block hc)

theorem WP.block_split {l₁ l₂ : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block (l₁ ++ l₂)) s Q) : WP isa (.block l₁) s fun t => WP isa (.block l₂) t Q := by
  obtain ⟨tr, t, e, hq⟩ := h
  have e' := exec_block_split e
  cases e' with
  | seq a b => exact ⟨_, _, a, _, _, b, hq⟩

theorem exec_bb {s t : State} {tr : List Leak} (e : Exec isa boundBits s tr t) :
    Exec isa (.seq bbA bbX) s tr t := by
  unfold boundBits at e
  cases e with
  | seq b1 e =>
    cases e with
    | seq b2 e =>
      cases e with
      | seq b3 e =>
        cases e with
        | seq b4 b5 =>
          have := Exec.seq (Exec.seq b1 (Exec.seq b2 (Exec.seq b3 b4))) b5
          simp only [List.append_assoc] at this
          exact this

theorem Exec.seq_inv {a b : Prog isa} {s t : State} {tr : List Leak} (e : Exec isa (.seq a b) s tr t) :
    ∃ t₁ u t₂, tr = t₁ ++ t₂ ∧ Exec isa a s t₁ u ∧ Exec isa b u t₂ t := by
  cases e with
  | seq h₁ h₂ => exact ⟨_, _, _, rfl, h₁, h₂⟩

theorem exec_main {s t : State} {tr : List Leak} (e : Exec isa main s tr t) : Exec isa mainG s tr t := by
  have e : Exec isa (.seq boundBits (.seq width (.seq metadata tail))) s tr t := e
  obtain ⟨a1, u1, a2, h1, eB, e⟩ := Exec.seq_inv e
  obtain ⟨b1, v1, b2, h2, eA, eX⟩ := Exec.seq_inv (exec_bb eB)
  obtain ⟨c1, u2, c2, h3, eW, e⟩ := Exec.seq_inv e
  obtain ⟨d1, v2, d2, h4, ew, ei⟩ := Exec.seq_inv (a := .block w1) (b := iteW) eW
  obtain ⟨e1, u3, e2, h5, eM, eT⟩ := Exec.seq_inv e
  obtain ⟨f1, v3, f2, h6, em, eM⟩ := Exec.seq_inv (a := .block m1) eM
  obtain ⟨g1, v4, g2, h7, er, el⟩ := Exec.seq_inv eM
  obtain ⟨i1, v5, i2, h8, el1, el2⟩ := Exec.seq_inv (exec_block_split (l₁ := [ldh .r30 hCtx]) (l₂ := mrest) el)
  have := Exec.seq eA (Exec.seq eX (Exec.seq ew (Exec.seq ei (Exec.seq em (Exec.seq er
    (Exec.seq el1 (Exec.seq el2 eT)))))))
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [List.append_assoc] at this ⊢
  exact this

theorem WP.main_G {s : State} {Q : State → Prop} (h : WP isa main s Q) : WP isa mainG s Q := by
  obtain ⟨tr, t, e, hq⟩ := h
  exact ⟨tr, t, exec_main e, hq⟩

theorem WP.bb {s : State} {Q : State → Prop} (h : WP isa boundBits s Q) : WP isa (.seq bbA bbX) s Q := by
  obtain ⟨tr, t, e, hq⟩ := h
  exact ⟨tr, t, exec_bb e, hq⟩

theorem RelCT.of_exec {P Q : State → State → Prop} {c c' : Prog isa}
    (hc : ∀ s tr t, Exec isa c' s tr t → Exec isa c s tr t) (h : RelCT isa P c Q) : RelCT isa P c' Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (hc _ _ _ e₁) (hc _ _ _ e₂)

/-! ## The pieces' registers -/

/-- `bbA`: the bound's first nonzero octet in `r14`, and `r15 = 0`. -/
theorem bbA_ok {s : State} {D : Addr} {k L : Nat} (h21 : s.gpr .r21 = D)
    (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hL : L = 2 * k ∨ L = 3 * k)
    (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) :
    WP isa bbA s fun t =>
      (t.gpr .r14 = BitVec.ofNat 64 (leadOct (VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L))) ∧
        t.gpr .r15 = BitVec.ofNat 64 0) ∧ Bignum.PPC64LE.Keep ([.r0, .r12] ++ scanRegs ++ [.r15]) s t := by
  unfold bbA
  refine WP.seq (WP.mono (boundPtr_ok h21 h27 h28 (by omega) hk32) fun s₁ ⟨⟨a12, m1⟩, k1⟩ => ?_)
  have hbytes : Spec.Rsa.bytesAt s₁.mem (bptr D k L) k =
      VG.Proof.Ffdh.KeyScalar.bnd k (Spec.Rsa.bytesAt s.mem D L) := by rw [m1, bptr_bnd _ _ hL]
  have hrdP : ∀ i < k, InRegions (s₁.rd ++ s₁.wr) (off (bptr D k L) i) 1 := fun i hi => by
    rw [k1.rd, k1.wr]
    unfold bptr
    split
    · rw [VG.Proof.Ffdh.PPC64LE.Domain.off_off']; exact hrd _ (by omega)
    · exact hrd _ (by omega)
  refine WP.seq (WP.mono (scan_ok hk hk32 hrdP a12 ((k1.gpr .r28 (by decide)).trans h28))
    fun u hu => WP.seq (WP.mono hu fun s₂ ⟨⟨_, a14, _⟩, k2⟩ => ?_))
  rw [hbytes] at a14
  refine WP.mono (Bignum.PPC64LE.WP.keep [.r15] (Q := fun t => t.gpr .r15 = BitVec.ofNat 64 0) (by prun) (by decide))
    fun t ⟨a15, k3⟩ => ⟨⟨?_, a15⟩, (k1.trans k2).trans k3⟩
  rw [k3.gpr .r14 (by decide), a14]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, leadOct]
  try omega

/-- `w1`: the recognized width in `r8`, and whether it is below `r16`'s. -/
theorem w1_ok {s : State} {S : Addr} {Z cap bl : Nat} (hs : Scr s S Z) (hZ : 104 ≤ Z) (h23 : s.gpr .r23 = S)
    (hcap : s.mem.readW (off S hCap) 64 = BitVec.ofNat 64 cap) (h16 : s.gpr .r16 = BitVec.ofNat 64 bl)
    (hc : cap < 2 ^ 32) (hb : bl < 2 ^ 32) :
    WP isa (.block w1) s fun t => (t.gpr .r8 = BitVec.ofNat 64 cap ∧
      t.gpr .r9 = BitVec.ofNat 64 (if cap < bl then 1 else 0)) ∧ Bignum.PPC64LE.Keep [.r8, .r9] s t := by
  have l96 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 96) 8 := by
    rw [h23]; exact hs.ld (d := 96) (n := 8) (by omega)
  have v96 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 96) 64 = BitVec.ofNat 64 cap := by rw [h23]; exact hcap
  refine Bignum.PPC64LE.WP.keep [.r8, .r9] ?_ (by decide)
  unfold w1 ldh
  prun [hCap, l96, v96, h16, lt_bit hc hb]

/-- `r30 :=` the context's address, from the header. -/
theorem ldh30_ok {s : State} {S C : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 8 ≤ Z) (h23 : s.gpr .r23 = S)
    (hC : s.mem.readW (off S hCtx) 64 = C) :
    WP isa (.block [ldh .r30 hCtx]) s fun t => t.gpr .r30 = C ∧ Bignum.PPC64LE.Keep [.r30] s t := by
  have l0 : InRegions (s.rd ++ s.wr) (s.gpr .r23 + BitVec.ofNat 64 0) 8 := by
    rw [h23]; exact hs.ld (d := 0) (n := 8) (by omega)
  have v0 : s.mem.readW (s.gpr .r23 + BitVec.ofNat 64 0) 64 = C := by rw [h23]; exact hC
  refine Bignum.PPC64LE.WP.keep [.r30] ?_ (by decide)
  unfold ldh
  prun [hCtx, l0, v0]

/-! ## What each piece reads -/

abbrev PQ.bd (q : PQ) : List Byte := VG.Proof.Ffdh.KeyScalar.bnd q.k q.db

/-- The bound's bit length. -/
abbrev PQ.bl (q : PQ) : Nat := 8 * (q.k - VG.Proof.Ffdh.lead q.bd - 1) + bitLength (leadOct q.bd)

/-- The width. -/
abbrev PQ.bits (q : PQ) : Nat := widthOf q.cap q.bl

abbrev PQ.rows (q : PQ) : Nat := Spec.Rsa.FixedBaseComb.rows q.bits

/-- The registers `Base` fixes, with their values. -/
def BV (q : PQ) (s : State) : Prop :=
  s.gpr .r10 = off q.S (slot q.w 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * q.w) ∧ s.gpr .r21 = q.D ∧
    s.gpr .r23 = q.S ∧ s.gpr .r27 = BitVec.ofNat 64 q.L ∧ s.gpr .r28 = BitVec.ofNat 64 q.k ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (q.w + 2)) ∧ s.gpr .r31 = q.S

theorem BV.of_base {q : PQ} {s : State} (h : Base q.cd s) : BV q s :=
  ⟨h.env.h10, h.env.h11, h.r21, h.r23, h.r27, h.r28, h.env.h29, h.env.h31⟩

theorem BV.keep {q : PQ} {s t : State} {rs : List Reg} (h : BV q s) (k : Bignum.PPC64LE.Keep rs s t)
    (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : BV q t := by
  obtain ⟨h10, h11, h21, h23, h27, h28, h29, h31⟩ := h
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  exact ⟨(k.gpr _ hr.1).trans h10, (k.gpr _ hr.2.1).trans h11, (k.gpr _ hr.2.2.1).trans h21,
    (k.gpr _ hr.2.2.2.1).trans h23, (k.gpr _ hr.2.2.2.2.1).trans h27, (k.gpr _ hr.2.2.2.2.2.1).trans h28,
    (k.gpr _ hr.2.2.2.2.2.2.1).trans h29, (k.gpr _ hr.2.2.2.2.2.2.2).trans h31⟩

theorem BV.pins {q : PQ} {s₁ s₂ : State} (h₁ : BV q s₁) (h₂ : BV q s₂) :
    ∀ r ∈ baseRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a10, a11, a21, a23, a27, a28, a29, a31⟩ := h₁
  obtain ⟨b10, b11, b21, b23, b27, b28, b29, b31⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a21, b21]
  · rw [a23, b23]
  · rw [a27, b27]
  · rw [a28, b28]
  · rw [a29, b29]
  · rw [a31, b31]

def V1 (q : PQ) (s : State) : Prop :=
  s.gpr .r14 = BitVec.ofNat 64 (leadOct q.bd) ∧ s.gpr .r15 = BitVec.ofNat 64 0 ∧ s.gpr .r23 = q.S
def V2 (q : PQ) (s : State) : Prop := s.gpr .r23 = q.S
def V3 (q : PQ) (s : State) : Prop :=
  s.gpr .r8 = BitVec.ofNat 64 q.cap ∧ s.gpr .r9 = BitVec.ofNat 64 (if q.cap < q.bl then 1 else 0) ∧
    s.gpr .r16 = BitVec.ofNat 64 q.bl ∧ s.gpr .r23 = q.S
def V4 (q : PQ) (s : State) : Prop := s.gpr .r16 = BitVec.ofNat 64 q.bits ∧ s.gpr .r23 = q.S
def V6 (q : PQ) (s : State) : Prop := BV q s ∧ s.gpr .r18 = BitVec.ofNat 64 q.rows
def V7 (q : PQ) (s : State) : Prop := BV q s ∧ s.gpr .r30 = q.C ∧ s.gpr .r18 = BitVec.ofNat 64 q.rows
def V8 (q : PQ) (s : State) : Prop := BV q s ∧ s.gpr .r30 = q.C ∧ s.gpr .r24 = BitVec.ofNat 64 q.rows

/-- From each piece on, the registers each later piece reads. -/
def C7 (q : PQ) (s : State) : Prop := WP isa (.block mrest) s fun t => V8 q t ∧ True
def C6 (q : PQ) (s : State) : Prop := WP isa (.block [ldh .r30 hCtx]) s fun t => V7 q t ∧ C7 q t
def C5 (q : PQ) (s : State) : Prop := WP isa rows s fun t => V6 q t ∧ C6 q t
def C4 (q : PQ) (s : State) : Prop := WP isa (.block m1) s fun t => V4 q t ∧ C5 q t
def C3 (q : PQ) (s : State) : Prop := WP isa iteW s fun t => V4 q t ∧ C4 q t
def C2 (q : PQ) (s : State) : Prop := WP isa (.block w1) s fun t => V3 q t ∧ C3 q t
def C1 (q : PQ) (s : State) : Prop := WP isa bbX s fun t => V2 q t ∧ C2 q t
def C0 (q : PQ) (s : State) : Prop := WP isa bbA s fun t => V1 q t ∧ C1 q t

theorem m1_ok (s : State) : WP isa (.block m1) s fun t => t.mem = s.mem ∧ Bignum.PPC64LE.Keep [.r17] s t := by
  refine Bignum.PPC64LE.WP.keep [.r17] ?_ (by decide)
  unfold m1
  prun

/-- `main`'s pieces read what `C0` says. -/
theorem main_pins {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) : C0 q s := by
  have mp := h.mp g
  have hb := h.1.1
  have bv := BV.of_base hb
  have hZ := mp.env.hZ
  have hk := g.hk; have hk' := g.hk'
  have hCn := mp.hc.nowrap
  have hdom : Spec.Rsa.bytesAt s.mem q.D q.L = q.db := hb.bD
  have hd : q.db.length = 2 * q.k ∨ q.db.length = 3 * q.k := by rw [g.hlen]; exact g.hL
  have hv' := (VG.Proof.Ffdh.domainValid_iff q.k q.db).mp g.dv
  have hpf := VG.Proof.Ffdh.PPC64LE.Domain.modulus_facts hv'.1
  have hmv := hv'.1
  have hnorm : 2 ^ (64 * ((q.k + 7) / 8 - 1)) ≤ Spec.Rsa.os2ip (q.db.take q.k) := by
    change 2 ^ (64 * ((q.k + 7) / 8 - 1)) ≤ (Spec.Ffdh.domainOf q.k q.db).p
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmv
    refine Nat.le_trans ?_ hmv.2
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hlead := lead_ne (by omega) hd g.dv
  have hcap := recognize_lt (by omega) hd hnorm
  have hlo : leadOct q.bd < 256 := (q.bd.getD (VG.Proof.Ffdh.lead q.bd) 0).isLt
  have hbl8 : bitLength (leadOct q.bd) ≤ 8 := bitLength_le_of_lt (by simpa using hlo)
  have hbl1 : 1 ≤ bitLength (leadOct q.bd) := bitLength_pos hlead
  have hbl : q.bl ≤ 8 * q.k := by simp only [PQ.bl]; omega
  have hbl1' : 1 ≤ q.bl := by simp only [PQ.bl]; omega
  have hcap' : q.cap ≤ 400 := hcap
  have hbits1 : 1 ≤ q.bits := by simp only [PQ.bits, widthOf]; split <;> omega
  have hbits : q.bits ≤ 8192 := by simp only [PQ.bits, widthOf]; split <;> omega
  have hBB := WP.bb (boundBits_ok mp.h21 mp.h27 mp.h28 mp.hL (by omega) (by omega) mp.rdD (by rw [hdom]; exact hlead))
  rw [WP.seq_iff] at hBB
  refine WP.mono (WP.and (bbA_ok mp.h21 mp.h27 mp.h28 mp.hL (by omega) (by omega) mp.rdD) hBB)
    fun s₁ ⟨⟨⟨a14, a15⟩, k1⟩, hX⟩ => ⟨⟨by rw [a14, hdom], a15, (k1.gpr .r23 (by decide)).trans mp.h23⟩, ?_⟩
  refine WP.mono hX fun s₂ ⟨⟨a16, m2⟩, k2⟩ => ⟨(k2.gpr .r23 (by decide)).trans mp.h23, ?_⟩
  rw [hdom] at a16
  replace a16 : s₂.gpr .r16 = BitVec.ofNat 64 q.bl := a16
  have g23 : s₂.gpr .r23 = q.S := (k2.gpr .r23 (by decide)).trans mp.h23
  have hcap2 : s₂.mem.readW (off q.S hCap) 64 = BitVec.ofNat 64 q.cap := by rw [m2]; have := mp.hcap; rw [hdom] at this; exact this
  have hs2 := mp.env.hs.congr k2.wr
  have hW := width_ok (cap := q.cap) hs2 (Nat.le_trans (by simp only [slot]; omega) hZ) g23 hcap2 a16
    (by omega) (by omega)
  unfold width at hW
  rw [WP.seq_iff] at hW
  refine WP.mono (WP.and (w1_ok hs2 (Nat.le_trans (by simp only [slot]; omega) hZ) g23 hcap2 a16 (by omega)
    (by omega)) hW) fun s₃ ⟨⟨⟨a8, a9⟩, k3⟩, hI⟩ =>
      ⟨⟨a8, a9, (k3.gpr .r16 (by decide)).trans a16, (k3.gpr .r23 (by decide)).trans g23⟩, ?_⟩
  refine WP.mono hI fun s₄ ⟨⟨a16', m4⟩, k4⟩ => ⟨⟨a16', (k4.gpr .r23 (by decide)).trans g23⟩, ?_⟩
  have g23' : s₄.gpr .r23 = q.S := (k4.gpr .r23 (by decide)).trans g23
  have k24 := k2.trans k4
  have m4' : s₄.mem = s.mem := by rw [m4, m2]
  have hc24 : Scr s₄ q.C 24 := ⟨let ⟨B₀, o, L', hm, hb, hL, hL'⟩ := (mp.hc.congr k24.wr).wr
    ⟨B₀, o, L', hm, hb, by unfold ctxWords at hL; omega, hL'⟩, by unfold ctxWords at hCn; omega⟩
  have hM := metadata_ok (mp.env.hs.congr k24.wr) (by simp only [slot] at hZ; omega) g23' (by rw [m4']; exact mp.hC)
    hc24 a16' hbits1 hbits
  unfold metadata at hM
  rw [WP.seq_iff] at hM
  refine WP.mono (WP.and (m1_ok s₄) hM) fun s₅ ⟨⟨m5, k5⟩, hR⟩ =>
    ⟨⟨(k5.gpr .r16 (by decide)).trans a16', (k5.gpr .r23 (by decide)).trans g23'⟩, ?_⟩
  rw [WP.seq_iff] at hR
  refine WP.mono (WP.and (rowsLoop_ok hbits1 (by omega) ((k5.gpr .r16 (by decide)).trans a16')) hR)
    fun s₆ ⟨⟨⟨a18, m6⟩, k6⟩, hL⟩ => ⟨⟨((((bv.keep k2).keep k4).keep k5).keep k6), a18⟩, ?_⟩
  have bv6 : BV q s₆ := ((((bv.keep k2).keep k4).keep k5).keep k6)
  have k26 := (k24.trans k5).trans k6
  have hL' := WP.block_split (l₁ := [ldh .r30 hCtx]) (l₂ := mrest) hL
  refine WP.mono (WP.and (ldh30_ok (mp.env.hs.congr k26.wr) (by simp only [slot] at hZ; omega) bv6.2.2.2.1
      (by rw [m6, m5, m4']; exact mp.hC)) hL')
    fun s₇ ⟨⟨a30, k7⟩, hMr⟩ => ⟨⟨bv6.keep k7, a30, (k7.gpr .r18 (by decide)).trans a18⟩, ?_⟩
  exact WP.mono hMr fun t ⟨⟨t30, t24, _⟩, kt⟩ => ⟨⟨(bv.keep k24).keep kt, t30, t24⟩, trivial⟩

end VG.Proof.Ffdh.PPC64LE.Cached
