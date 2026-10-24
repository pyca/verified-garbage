module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeFn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeBody
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeBody

/-!
# `vg_ffdh_exchange` on PPC64LE: constant time

As `CheckDomainCT.lean`, with the public data `XD`: the domain's and the
peer's (`CD`, its y the peer), and the addresses of `out` and x and x's
length, but not x's bytes. The predicates fix what the code branches on,
p's validity, and the registers that the code loads back from memory, which
the taint analysis treats as secret: the working space's address from the
stack, x's address and length and `out`'s address from the header. Where
the code computes from x (`exPre`, the power, `exOutPre` and the output),
each predicate states the registers the next piece needs and that the rest
of the code reaches the next predicate (`exPower_split`, `exOut_split`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot bytesAt_length)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The public data of an exchange: the domain and the peer (`c`, whose `Y`
is the peer), `out` and x's address and length. -/
structure XD where
  c : CD
  O : Addr
  X : Addr
  xl : Nat

def xdOf (s : State) : XD :=
  ⟨⟨s.gpr .r5, s.gpr .r10, stackArg s 1, (s.gpr .r7).toNat, (s.gpr .r6).toNat, (stackArg s 2).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat⟩,
    s.gpr .r3, s.gpr .r8, (s.gpr .r9).toNat⟩

/-- What holds of the peer, x and `out` from the header's stores on. -/
structure Ext (x : XD) (s : State) : Prop where
  r9 : s.gpr .r9 = x.c.Y
  wX : s.mem.readW (off x.c.S 64) 64 = off x.X 0
  wXL : s.mem.readW (off x.c.S 72) 64 = BitVec.ofNat 64 x.xl
  wO : s.mem.readW (off x.c.S 80) 64 = off x.O 0
  rdX : ∀ i < x.xl, InRegions (s.rd ++ s.wr) (off x.X i) 1
  sepX : ∀ i < x.xl, ∀ y, ofs x.c.S y < x.c.Z → off x.X i ≠ y
  scrO : Scr s x.O x.c.k
  sepO : ∀ y, ofs x.O y < x.c.k → x.c.Z ≤ ofs x.c.S y
  xl1 : 1 ≤ x.xl
  xlk : x.xl ≤ x.c.k

theorem Ext.keep {x : XD} {s t : State} {rs : List Reg} (h : Ext x s) (k : Keep rs s t)
    (hm : Body x.c.S x.c.w s.mem t.mem) (hr : Reg.r9 ∉ rs := by decide) : Ext x t where
  r9 := (k.gpr _ hr).trans h.r9
  wX := by
    have := slot_eq x.c.w 0
    show word t.mem x.c.S 64 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wX
  wXL := by
    have := slot_eq x.c.w 0
    show word t.mem x.c.S 72 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wXL
  wO := by
    have := slot_eq x.c.w 0
    show word t.mem x.c.S 80 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wO
  rdX := by rw [k.rd, k.wr]; exact h.rdX
  sepX := h.sepX
  scrO := h.scrO.congr k.wr
  sepO := h.sepO
  xl1 := h.xl1
  xlk := h.xlk

theorem Ext.same {x : XD} {s t : State} {rs : List Reg} (h : Ext x s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : Reg.r9 ∉ rs := by decide) : Ext x t :=
  h.keep k (by rw [hm]; exact Outside.refl _ _ _ _) hr

/-! ## The predicates -/

def X0 (x : XD) (s : State) : Prop := exContract.pre s ∧ xdOf s = x

/-- After loading the working space's address. -/
def L1 (x : XD) (s : State) : Prop :=
  ∃ s₀, X0 x s₀ ∧ s.gpr .r11 = stackArg s₀ 1 ∧ s.mem = s₀.mem ∧ Keep [.r11] s₀ s

/-- From `setup` on. -/
def XB (x : XD) (s : State) : Prop := Base x.c s ∧ Ext x s

/-- With `loadN`'s arguments. -/
def X1a (x : XD) (s : State) : Prop := XB x s ∧ s.gpr .r12 = off x.c.D 0 ∧ s.gpr .r6 = BitVec.ofNat 64 x.c.k

/-- After `loadN`. -/
def X2 (x : XD) (s : State) : Prop := X1a x s ∧ arr s.mem x.c.S x.c.w 0 = x.c.p

/-- After `check1`. -/
def X3 (x : XD) (s : State) : Prop :=
  XB x s ∧ arr s.mem x.c.S x.c.w 0 = x.c.p ∧ s.gpr .r6 = BitVec.ofNat 64 x.c.k ∧
    s.gpr .r15 = BitVec.ofNat 64 ((x.c.db.take x.c.k).getD 0 0).toNat ∧ s.gpr .r18 = 1 ∧
    (s.gpr .r0 = 0 ↔ ((x.c.db.take x.c.k).getD (x.c.k - 1) 0).toNat % 2 = 1)

/-- After `check2`. -/
def X4 (x : XD) (s : State) : Prop :=
  XB x s ∧ arr s.mem x.c.S x.c.w 0 = x.c.p ∧ (s.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid x.c.p x.c.k = true)

/-- Before the output: its registers, and that it ends with the working
space in `r23`. -/
def X7 (x : XD) (s : State) : Prop :=
  (s.gpr .r27 = off x.O 0 ∧ s.gpr .r10 = off x.c.S (slot x.c.w 0) ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (x.c.w + 2)) ∧ s.gpr .r28 = BitVec.ofNat 64 x.c.k ∧ s.gpr .r23 = x.c.S ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * x.c.w)) ∧
  WP isa PublicChecked.output s (CF x.c)

/-- After the power: the registers of `exOutPre`, and that it reaches `X7`. -/
def X6 (x : XD) (s : State) : Prop :=
  (s.gpr .r10 = off x.c.S (slot x.c.w 0) ∧ s.gpr .r29 = BitVec.ofNat 64 (8 * (x.c.w + 2)) ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * x.c.w) ∧ s.gpr .r23 = x.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 x.c.k) ∧
  WP isa exOutPre s (X7 x)

/-- After `exPre`: the power's registers, and that it reaches `X6`. -/
def X5 (x : XD) (s : State) : Prop :=
  (s.gpr .r30 = off x.X 0 ∧ s.gpr .r31 = BitVec.ofNat 64 x.xl ∧ s.gpr .r10 = off x.c.S (slot x.c.w 0) ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (x.c.w + 2)) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * x.c.w) ∧
    s.gpr .r23 = x.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 x.c.k) ∧
  WP isa ModExp.powSecret s (X6 x)

/-- `Pins` from registers that the predicate fixes as functions of the data. -/
theorem pins_of {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a _ _ h₁ h₂ r hr => (h a _ h₁ r hr).trans (h a _ h₂ r hr).symm

theorem pins_XB {Φ : XD → State → Prop} (h : ∀ x s, Φ x s → XB x s) :
    Pins Φ (baseRegs ++ ([.r9] : List Reg)) := by
  intro x s₁ s₂ h₁ h₂ r hr
  have h₁ := h _ _ h₁
  have h₂ := h _ _ h₂
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.pins h₂.1 r hr
  · rw [List.mem_singleton] at hr; subst hr; rw [h₁.2.r9, h₂.2.r9]

theorem pins_X1a {Φ : XD → State → Prop} (h : ∀ x s, Φ x s → X1a x s) :
    Pins Φ (baseRegs ++ ([.r12, .r6] : List Reg)) := by
  intro x s₁ s₂ h₁ h₂ r hr
  have h₁ := h _ _ h₁
  have h₂ := h _ _ h₂
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

theorem pins_X3 : Pins X3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := by
  intro x s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]

theorem pins_L1 : Pins L1 [.r11] := pins_of (fun x _ => x.c.S) fun x s h r hr => by
  obtain ⟨s₀, ⟨_, hx⟩, a11, _⟩ := h
  rw [List.mem_singleton] at hr; subst hr
  rw [a11, ← hx]; rfl

theorem pins_X5 : Pins X5 [.r10, .r11, .r23, .r28, .r29, .r30, .r31] :=
  pins_of (fun x r => match r with
      | .r10 => off x.c.S (slot x.c.w 0) | .r11 => BitVec.ofNat 64 (2 * x.c.w) | .r23 => x.c.S
      | .r28 => BitVec.ofNat 64 x.c.k | .r29 => BitVec.ofNat 64 (8 * (x.c.w + 2)) | .r30 => off x.X 0
      | _ => BitVec.ofNat 64 x.xl) fun x s h r hr => by
    obtain ⟨⟨a30, a31, a10, a29, a11, a23, a28⟩, _⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pins_X6 : Pins X6 [.r10, .r11, .r23, .r28, .r29] :=
  pins_of (fun x r => match r with
      | .r10 => off x.c.S (slot x.c.w 0) | .r11 => BitVec.ofNat 64 (2 * x.c.w) | .r23 => x.c.S
      | .r28 => BitVec.ofNat 64 x.c.k | _ => BitVec.ofNat 64 (8 * (x.c.w + 2))) fun x s h r hr => by
    obtain ⟨⟨a10, a29, a11, a23, a28⟩, _⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pins_X7 : Pins X7 [.r10, .r11, .r23, .r27, .r28, .r29] :=
  pins_of (fun x r => match r with
      | .r10 => off x.c.S (slot x.c.w 0) | .r11 => BitVec.ofNat 64 (2 * x.c.w) | .r23 => x.c.S
      | .r27 => off x.O 0 | .r28 => BitVec.ofNat 64 x.c.k | _ => BitVec.ofNat 64 (8 * (x.c.w + 2)))
    fun x s h r hr => by
    obtain ⟨⟨a27, a10, a29, a28, a23, a11⟩, _⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pins_XCF : Pins (fun (x : XD) s => CF x.c s) [.r23] :=
  pins_of (fun x _ => x.c.S) fun x s h r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact h

/-! ## The front, by correctness -/

theorem XL1 {x : XD} {s : State} (h : X0 x s) :
    WP isa (.block ([.addSp .r11 104, .load .d .r11 .r11 0] : List Instr)) s (L1 x) := by
  obtain ⟨hpre, hx⟩ := h
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨exStack s, List.mem_append_left _ (by rw [hpre.2.1]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 104) 8
    rw [show s.sp + BitVec.ofNat 64 104 = s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [Offset.add_add]]
    exact Offset.contains_base _ (by omega) (by omega)
  exact WP.mono (loadS1_ok s hA1) fun t ⟨⟨a11, m⟩, k⟩ => ⟨s, ⟨hpre, hx⟩, a11, m, k⟩

theorem XF {x : XD} {s : State} (h : L1 x s) :
    WP isa (.block (save .r11 ++ (([.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r3 .r23 80,
      .addi .r9 .r10 0, .addi .r3 .r5 0, .addi .r4 .r6 0, .addi .r5 .r7 0] : List Instr) ++ setup))) s (XB x) := by
  obtain ⟨s₀, ⟨⟨hsp, hrd, hwr, dOD, dOX, dOP, dOS, dOA, dDS, dXS, dPS, dSA, nwO, nwD, nwX, nwP, nwS, ⟨hk, hk'⟩, hL,
    hol, hpl, hx1, hxk, hsl⟩, rfl⟩, a11, m0, k0⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [xdOf]
  rw [hol] at hwr dOD dOX dOP dOS dOA nwO
  rw [hpl] at hrd dOP dPS nwP ⊢
  generalize hOd : s₀.gpr .r3 = O at hwr dOD dOX dOP dOS dOA nwO ⊢
  generalize hDd : s₀.gpr .r5 = D at hrd dOD dDS nwD ⊢
  generalize hLd : (s₀.gpr .r6).toNat = L at hrd dOD dDS nwD hL ⊢
  generalize hkd : (s₀.gpr .r7).toNat = k at hk hk' hL hxk hsl hwr dOD dOX dOP dOS dOA nwO hrd dPS nwP ⊢
  generalize hXd : s₀.gpr .r8 = X at hrd dOX dXS nwX ⊢
  generalize hxd : (s₀.gpr .r9).toNat = xl at hrd dOX dXS nwX hx1 hxk ⊢
  generalize hPd : s₀.gpr .r10 = P at hrd dOP dPS nwP ⊢
  generalize hSd : stackArg s₀ 1 = S at hwr dOS dDS dXS dPS dSA nwS a11 ⊢
  generalize hZd : (stackArg s₀ 2).toNat * 8 = Z at hwr dOS dDS dXS dPS dSA nwS ⊢
  have hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have hZ256 : 256 ≤ Z := by omega
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s₀ S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s₀.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have hinH : ∀ i < 3, InRegions s₀.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (ws := .r11) (by decide) s (by rw [a11, k0.wr]; exact hin)) fun s₁ hS => ?_
  have k1 := k0.trans hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans a11
  have hfr₁ : Frame [savR S] s₀.mem s₁.mem := by rw [← m0, ← a11]; exact hS.frame
  rw [WP.block_append_iff]
  refine WP.mono (hdr_ok h23₁ (by rw [k1.wr]; exact hinH)) fun s₂ ⟨⟨w8, w9, w10, b9, b3, b4, b5, o2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) (b3.trans ((k1.gpr .r5 (by decide)).trans hDd))
    (by rw [b4, k1.gpr .r6 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [b5, k1.gpr .r7 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans h23₁) hk') fun s₃ ⟨⟨a21, a27, a28, a11', a29, a10, a31, m3⟩, k3⟩ => ?_
  have k123 := k12.trans k3
  have hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt s₃.mem Q n = Spec.Rsa.bytesAt s₀.mem Q n := fun Q n hsep => by
    rw [m3, outside_bytesAt o2 (by omega) hsep]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hfr₁ _ fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    have hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega)) _ hc
    exact hsep i (List.mem_range.mp hi) _ (by simp only [Region.Contains] at hc'; exact hc') rfl
  have sepD := sep_of_disjoint dDS (by omega)
  have sepP := sep_of_disjoint dPS (by omega)
  have hw3 : ∀ d, word s₃.mem S d = word s₂.mem S d := fun d => by rw [m3]
  refine ⟨⟨⟨hs.congr k123.wr, a10, a29, a11', a31, show 4 ≤ (k + 7) / 8 by omega,
    show (k + 7) / 8 ≤ 128 by omega, hZw⟩, a21, (k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁),
    a27, a28, hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega,
    fun i hi => by rw [k123.rd, k123.wr]; exact rd_of_mem (s := s₀) (D := D) (L := L) (by rw [hrd]; simp) (by omega) i hi,
    sepD,
    fun i hi => by rw [k123.rd, k123.wr]; exact rd_of_mem (s := s₀) (D := P) (L := k) (by rw [hrd]; simp) (by omega) i hi,
    sepP, hb3 D L sepD, hb3 P k sepP⟩, ⟨?_, ?_, ?_, ?_,
    fun i hi => by rw [k123.rd, k123.wr]; exact rd_of_mem (s := s₀) (D := X) (L := xl) (by rw [hrd]; simp) (by omega) i hi,
    sep_of_disjoint (L := xl) dXS (by omega), Scr.of_mem (by rw [k123.wr, hwr]; simp) nwO, Pub.sep_of_disjoint dOS, hx1, hxk⟩⟩
  · rw [k3.gpr .r9 (by decide), b9, k1.gpr .r10 (by decide), hPd]
  · show word s₃.mem S 64 = _
    rw [hw3, w8, k1.gpr .r8 (by decide), hXd]; simp [off]
  · show word s₃.mem S 72 = _
    rw [hw3, w9, k1.gpr .r9 (by decide), ← hxd, VG.Proof.Bignum.ofNat_toNat64]
  · show word s₃.mem S 80 = _
    rw [hw3, w10, k1.gpr .r3 (by decide), hOd]; simp [off]

/-! ## p's check, by correctness -/

theorem XA {x : XD} {s : State} (h : XB x s) :
    WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (X1a x) := by
  refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off x.c.D 0 ∧ t.gpr .r6 = BitVec.ofNat 64 x.c.k ∧
    t.mem = s.mem) (by prun [h.1.r21, h.1.r28, BitVec.add_zero]) (by decide)) fun t ⟨⟨a12, a6, m⟩, k⟩ =>
      ⟨⟨h.1.same k m, h.2.same k m⟩, a12, a6⟩

theorem XL {x : XD} {s : State} (h : X1a x s) : WP isa Precompute.loadN s (X2 x) := by
  obtain ⟨⟨hb, he⟩, h12, h6⟩ := h
  have hwd : x.c.w = (x.c.k + 7) / 8 := rfl
  have hZ := hb.env.hZ
  have hk := hb.k64
  have hk' := hb.k1024
  have hnw := hb.env.hs.nowrap
  have e28 := slot_eq x.c.w 28
  refine WP.mono (loadN_ok (dA := slot x.c.w 0) hb.env.hs hb.env.h10 h12 h6 hb.env.h11 (by omega) (by omega)
    (by omega) (by rw [slot_eq]; omega) (by rw [slot_eq] at hZ ⊢; omega)
    (fun i hi => hb.rdD i (by rcases hb.hL with h | h <;> omega))
    (fun i hi => hb.sepD i (by rcases hb.hL with h | h <;> omega))) fun t ⟨hv, out, k⟩ => ?_
  have hm : Body x.c.S x.c.w s.mem t.mem := Body.of out (Nat.le_refl _) (by rw [slot_eq] at hZ ⊢; omega)
  refine ⟨⟨⟨hb.keep k hm, he.keep k hm⟩, (k.gpr .r12 (by decide)).trans h12, (k.gpr .r6 (by decide)).trans h6⟩, ?_⟩
  rw [arr, hv, ← Proof.Ffdh.take_bytesAt _ _ (show x.c.k ≤ x.c.L by rcases hb.hL with h | h <;> omega), hb.bD]

theorem XC1 {x : XD} {s : State} (h : X2 x s) : WP isa (.block Precompute.check1) s (X3 x) := by
  obtain ⟨⟨⟨hb, he⟩, h12, h6⟩, hp⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := x.c.D) (nb := x.c.db.take x.c.k) h12 h6 hk hl
    (fun i hi => hb.rdD i (by have := hb.kL; omega)) fun i hi => hb.take_byte hi)
    fun t ⟨⟨i0, i15, i18, im⟩, k⟩ => ⟨⟨hb.same k im, he.same k im⟩, by rw [arr, im]; exact hp,
      (k.gpr .r6 (by decide)).trans h6, by rw [i15, getD_of_lt' (by omega)], i18,
      by rw [i0, getD_of_lt' (by omega)]⟩

theorem XC2 {x : XD} {s : State} (h : X3 x s) : WP isa Precompute.check2 s (X4 x) := by
  obtain ⟨⟨hb, he⟩, hp, h6, h15, h18, h0⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check2_ok (nb := x.c.db.take x.c.k) h6 hk hb.k1024 hl (by rw [h0, getD_of_lt' (by omega)])
    (by rw [h15, getD_of_lt' (by omega)]) h18) fun t ⟨a, m, k⟩ =>
    ⟨⟨hb.same k m, he.same k m⟩, by rw [arr, m]; exact hp, a⟩

/-! ## After p's check -/

theorem T5 {x : XD} {s : State} (h : X4 x s ∧ s.gpr .r0 = 0) : WP isa exPre s (X5 x) := by
  obtain ⟨⟨⟨hb, he⟩, hp, h0⟩, hz⟩ := h
  have hv := h0.mp hz
  have hf := modulus_facts hv
  have hk := hb.k64
  have hk' := hb.k1024
  have hxk := he.xlk
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have e0 := slot_eq x.c.w 0
  have e28 := slot_eq x.c.w 28
  have hwd : x.c.w = (x.c.k + 7) / 8 := rfl
  have hpk : x.c.p < 256 ^ x.c.k := by
    have := VG.Proof.Bignum.os2ip_lt (x.c.db.take x.c.k)
    rwa [hb.take_len] at this
  refine WP.mono (exPower_split hb.env hb.r23 he.r9 hb.r28 (by omega) (by omega) he.xl1 (by omega) hb.rdY hb.sepY
    he.rdX he.sepX he.wX he.wXL (by rw [hp]; exact hf.1) (by rw [hp]; exact hf.2))
    fun s₆ ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, hw⟩ => ⟨⟨a30, a31, g10, g29, g11, g23, g28⟩, WP.mono hw
      fun t ⟨⟨z5, p5, b5, r10₅⟩, k5⟩ => ?_⟩
  have k29 := (k5.gpr .r29 (by decide)).trans hb.env.h29
  have k11 := (k5.gpr .r11 (by decide)).trans hb.env.h11
  have k23 := (k5.gpr .r23 (by decide)).trans hb.r23
  have k28 := (k5.gpr .r28 (by decide)).trans hb.r28
  refine ⟨⟨r10₅, k29, k11, k23, k28⟩, WP.mono (exOut_split (O := x.O) (hb.env.hs.congr k5.wr) (he.scrO.congr k5.wr)
    r10₅ k29 k11 k23 k28 hb.env.hw hb.env.hw' hZ (by omega) (by omega) ?_ he.sepO (by rw [p5, hp]; omega)
    (by rw [z5, p5]; exact Nat.mod_lt _ (by rw [hp]; omega)) (by rw [p5, hp]; exact hpk))
    fun s₃ ⟨⟨a27, b10, b29, b28, b23, b11⟩, hw'⟩ => ⟨⟨a27, b10, b29, b28, b23, b11⟩, WP.mono hw'
      fun u ⟨_, ku⟩ => (ku.gpr .r23 (by decide)).trans k23⟩⟩
  show word t.mem x.c.S 80 = _
  rw [Outside.word b5 (Or.inl (by omega)) (by omega)]; exact he.wO

/-- 0 into `r3`, without a valid p. -/
theorem TK0x {x : XD} {s : State} (h : X4 x s ∧ s.gpr .r0 ≠ 0) : WP isa (.block [.li .r3 0]) s (CF x.c) :=
  TK0 (Φ := fun d s => Base d s) (fun _ _ h => h) h.1.1.1

/-! ## Constant time -/

theorem pins_X0 : Pins X0 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem ex_rel : RelCT isa (Two X0) exchange fun _ _ => True := by
  unfold exchange exFront
  simp only [List.append_assoc]
  refine RelCT.seq (R := Two XB) ?_ (RelCT.seq (R := Two X4) ?_
    (RelCT.seq (R := Two fun (x : XD) s => CF x.c s) ?_ (two_taint _ pins_XCF (by taint_decide))))
  · exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_X0 (by taint_decide)) fun _ _ h => XL1 h)
      (two_post (two_taint _ pins_L1 (by taint_decide)) fun _ _ h => XF h))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_XB (Φ := XB) fun _ _ h => h) (by taint_decide)) fun _ _ h => XA h)
      (RelCT.seq (two_post (two_taint _ (pins_X1a fun _ _ h => h) (by taint_decide)) fun _ _ h => XL h)
        (RelCT.seq (two_post (two_taint (Φ := X2) _ (pins_X1a fun _ _ h => h.1) (by taint_decide))
          fun _ _ h => XC1 h)
          (two_post (two_taint _ pins_X3 (by taint_decide)) fun _ _ h => XC2 h)))
  · refine two_ite (Φ := X4) (fun x s₁ s₂ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_
      (two_post (two_taint _ (pins_XB (Φ := fun x s => X4 x s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1)
        (by taint_decide)) fun _ _ h => TK0x h)
    unfold exPower exOut
    exact RelCT.seq (RelCT.seq (two_post (two_taint _ (pins_XB (Φ := fun x s => X4 x s ∧ s.gpr .r0 = 0)
        fun _ _ h => h.1.1) (by taint_decide)) fun _ _ h => T5 h)
      (two_post (two_taint _ pins_X5 (by taint_decide)) fun _ _ h => h.2))
      (RelCT.seq (two_post (two_taint _ pins_X6 (by taint_decide)) fun _ _ h => h.2)
        (two_post (two_taint _ pins_X7 (by taint_decide)) fun _ _ h => h.2))

theorem ex_ct : ConstantTime isa exContract.pre exContract.pub exchange :=
  RelCT.constantTime (ex_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, hb⟩ =>
    ⟨xdOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [exLeak] at hb
      obtain ⟨e12, -⟩ := List.append_inj hb (by simp only [List.length_append, List.length_map, bytesAt_length, h6, a0])
      obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [List.length_map, bytesAt_length, h6])
      simp only [xdOf]
      rw [(List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1,
        (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e2]
      simp only [h3, h5, h6, h7, h8, h9, h10, a1, a2]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.Domain
