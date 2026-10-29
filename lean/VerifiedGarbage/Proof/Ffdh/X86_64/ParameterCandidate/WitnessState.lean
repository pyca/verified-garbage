module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # FFDH parameter generation on x86-64: rejection-loop state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.MlKem.X86_64

structure WitnessParams where
  O : Addr
  Z : Nat
  op : Addr
  bits : Nat
  w : Nat
  N : Nat
  mi : BitVec 64
  bits1 : 511 ≤ bits
  bits2 : bits ≤ 8192
  width : w = (((bits + 7) / 8) + 7) / 8
  room : 256 + slot w 28 ≤ Z
  predBits : Spec.RsaKeyGen.bitLength (N - 1) = bits
  odd : N % 2 = 1
  n3 : 3 ≤ N

def WitnessParams.I (p : WitnessParams) : Addr := off p.O 256
def WitnessParams.IZ (p : WitnessParams) : Nat := p.Z - 256
def WitnessParams.len (p : WitnessParams) : Nat := (p.bits + 7) / 8

theorem WitnessParams.width_bounds (p : WitnessParams) :
    4 ≤ p.w ∧ p.w ≤ 128 ∧ 2 ≤ p.len ∧ p.len ≤ 1024 ∧ p.bits ≤ 64 * p.w := by
  have hb1 := p.bits1
  have hb2 := p.bits2
  have hw := p.width
  unfold WitnessParams.len
  omega

theorem WitnessParams.dims (p : WitnessParams) : MrDims p.I p.IZ p.w := by
  have hr : 256 + (256 + 28 * (8 * (p.w + 2))) ≤ p.Z := p.room
  have hw := p.width_bounds
  refine ⟨?_, ?_, hw.1, hw.2.1⟩
  · change 256 + 8 * (8 * (p.w + 2)) ≤ p.Z - 256
    omega_using [hr]
  · change 256 + 26 * (8 * (p.w + 2)) + 8 * (p.w + 2) ≤ p.Z - 256
    omega_using [hr]

theorem WitnessParams.octets (p : WitnessParams) : Spec.Ffdh.witnessOctets p.N = p.len := by
  simp only [Spec.Ffdh.witnessOctets, p.predBits, WitnessParams.len]

theorem WitnessParams.space_bounds (p : WitnessParams) :
    256 ≤ p.Z ∧ 136 ≤ p.IZ ∧ 256 + p.IZ = p.Z := by
  have hr : 256 + (256 + 28 * (8 * (p.w + 2))) ≤ p.Z := p.room
  unfold WitnessParams.IZ
  omega_using [hr]

theorem inner_header {p : WitnessParams} {m m' : Mem} {rs : List (Nat × Nat)}
    (hf : Frm p.I rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.IZ) (hz : p.Z ≤ 2 ^ 64) :
    ∀ j < 32, word m' p.O (8 * j) = word m p.O (8 * j) := by
  intro j hj
  exact hf.word_below hrs (by omega_using [p.space_bounds.2.2, hz]) (by decide) (by omega)

theorem inner_link {p : WitnessParams} {m m' : Mem} {rs : List (Nat × Nat)}
    (hf : Frm p.I rs m m') (hrs : ∀ r ∈ rs, 136 ≤ r.1) :
    word m' p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = word m p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) :=
  hf.word_eq (fun r hr => Or.inl (hrs r hr)) (by decide)

theorem keep_modulus {s t : State} (k : Keep (.rdi :: mmRegs) s t)
    (hdi : t.gpr .rdi = s.gpr .rdi) : Keep mmRegs s t := by
  refine ⟨?_, k.2⟩
  intro r hr
  by_cases hd : r = .rdi
  · subst hd; exact hdi
  · exact k.gpr (by simp only [List.mem_cons, not_or]; exact ⟨hd, hr⟩)

/-- All memory outside the working space and the witness buffer is unchanged. -/
def DrawFrame (p : WitnessParams) (m m' : Mem) : Prop :=
  ∀ a, p.Z ≤ ofs p.O a → (∀ i < p.len, a ≠ off p.op i) → m' a = m a

/-- Every outer word except the tape counters and status is preserved. -/
def DrawSaved (p : WitnessParams) (m m' : Mem) : Prop :=
  ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 → j ≠ 19 → word m' p.O (8 * j) = word m p.O (8 * j)

theorem DrawSaved.refl (p : WitnessParams) (m : Mem) : DrawSaved p m m := fun _ _ _ _ _ _ => rfl

theorem DrawSaved.trans {p : WitnessParams} {m₁ m₂ m₃ : Mem}
    (h : DrawSaved p m₁ m₂) (h' : DrawSaved p m₂ m₃) : DrawSaved p m₁ m₃ :=
  fun j hj h12 h13 h14 h19 => (h' j hj h12 h13 h14 h19).trans (h j hj h12 h13 h14 h19)

theorem DrawFrame.refl (p : WitnessParams) (m : Mem) : DrawFrame p m m := fun _ _ _ => rfl

theorem DrawFrame.trans {p : WitnessParams} {m₁ m₂ m₃ : Mem}
    (h : DrawFrame p m₁ m₂) (h' : DrawFrame p m₂ m₃) : DrawFrame p m₁ m₃ :=
  fun a ha ho => (h' a ha ho).trans (h a ha ho)

theorem DrawFrame.of_scr {p : WitnessParams} {m m' : Mem} (h : InScr p.O p.Z m m') :
    DrawFrame p m m' := fun a ha _ => h a ha

theorem DrawFrame.of_bytes {p : WitnessParams} {m m' : Mem}
    (h : ∀ a, (∀ i < p.len, a ≠ off p.op i) → m' a = m a) : DrawFrame p m m' :=
  fun a _ ho => h a ho

theorem DrawFrame.of_inner {p : WitnessParams} {m m' : Mem} {rs : List (Nat × Nat)}
    (h : Frm p.I rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.IZ) (hz : p.Z ≤ 2 ^ 64) :
    DrawFrame p m m' := by
  have hshift : Frm p.O (shiftRanges 256 rs) m m' :=
    h.rebase (by decide) (fun r hr => by have := hrs r hr; unfold WitnessParams.IZ at this; omega)
  apply DrawFrame.of_scr (InScr.of_frm hshift ?_)
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  have hfit := hrs r' hr'
  have hsize : 256 ≤ p.Z := by have := p.room; omega
  dsimp only
  unfold WitnessParams.IZ at hfit
  omega

theorem output_inner {p : WitnessParams} {s : State} (h : OutOk s p.O p.Z p.op p.len)
    (hz : p.Z ≤ 2 ^ 64) : OutOk s p.I p.IZ p.op p.len := by
  refine ⟨h.wr, ?_⟩
  intro i hi
  have ho := h.sep i hi
  rcases ofs_rebase p.O (p.op + BitVec.ofNat 64 i) (o := 256) (by decide) with ⟨_, he⟩ | ⟨_, he⟩
  · change p.Z - 256 ≤ ofs (off p.O 256) (p.op + BitVec.ofNat 64 i)
    rw [he]
    omega_using [ho]
  · change p.Z - 256 ≤ ofs (off p.O 256) (p.op + BitVec.ofNat 64 i)
    omega_using [hz, he]

/-- The loop owns the tape position, the masked output buffer, and Xm.
All precomputation is retained across retries and accepted witnesses. -/
structure DrawState (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (s : State) : Prop where
  scr : Scr s p.O p.Z
  ready : ModulusReady s p.I p.IZ p.w p.mi p.N
  link : word s.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O
  outPtr : word s.mem p.O (8 * oOut) = p.op
  bits : word s.mem p.O (8 * oWitnessBits) = BitVec.ofNat 64 p.bits
  len : word s.mem p.O (8 * oWitnessLen) = BitVec.ofNat 64 p.len
  ptr : word s.mem p.O (8 * oRandPtr) = rp
  left : word s.mem p.O (8 * oRandLeft) = BitVec.ofNat 64 bs.length
  usedWord : word s.mem p.O (8 * oUsed) = BitVec.ofNat 64 used
  countBound : used + bs.length < 2 ^ 64
  rand : Src s p.O p.Z rp bs
  out : OutOk s p.O p.Z p.op p.len
  apart : Apart p.op p.len rp bs.length

/-- The random source survives every write permitted to the draw loop. -/
theorem DrawState.source_frame {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s t : State}
    {regs : List Reg} (h : DrawState p rp used bs s) (hf : DrawFrame p s.mem t.mem) (k : Keep regs s t) :
    Src t p.O p.Z rp bs := by
  refine ⟨fun i hi => by rw [k.2.1, k.2.2]; exact h.rand.rd i hi, ?_, h.rand.out⟩
  intro i hi
  rw [hf _ (h.rand.out i hi) (fun j hj he => h.apart j hj i hi he.symm)]
  exact h.rand.val i hi

theorem DrawState.transport {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s t : State}
    {regs : List Reg} (h : DrawState p rp used bs s)
    (hr : ModulusReady t p.I p.IZ p.w p.mi p.N)
    (hl : word t.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O)
    (hh : ∀ j < 32, j ≠ oStatus → word t.mem p.O (8 * j) = word s.mem p.O (8 * j))
    (hf : DrawFrame p s.mem t.mem) (k : Keep regs s t) : DrawState p rp used bs t := by
  refine ⟨h.scr.congr k.2.2, hr, hl, ?_, ?_, ?_, ?_, ?_, ?_, h.countBound, h.source_frame hf k,
    ⟨fun i hi => by rw [k.2.2]; exact h.out.wr i hi, h.out.sep⟩, h.apart⟩
  · exact (hh _ (by decide) (by decide)).trans h.outPtr
  · exact (hh _ (by decide) (by decide)).trans h.bits
  · exact (hh _ (by decide) (by decide)).trans h.len
  · exact (hh _ (by decide) (by decide)).trans h.ptr
  · exact (hh _ (by decide) (by decide)).trans h.left
  · exact (hh _ (by decide) (by decide)).trans h.usedWord

theorem DrawState.same_mem {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s t : State}
    {regs : List Reg} (h : DrawState p rp used bs s) (hm : t.mem = s.mem)
    (k : Keep regs s t) (hdi : t.gpr .rdi = p.I) : DrawState p rp used bs t := by
  apply h.transport (h.ready.of_words p.dims (by intro d _; rw [hm]) k.2.2 hdi)
    (by rw [hm]; exact h.link) (by intro j _ _; rw [hm])
    (by rw [hm]; exact DrawFrame.refl _ _) k

theorem DrawState.status_write {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s t : State}
    {regs : List Reg} (h : DrawState p rp used bs s) (v : BitVec 64)
    (hm : t.mem = s.mem.writeW (off p.O (8 * oStatus)) v)
    (k : Keep regs s t) (hdi : t.gpr .rdi = p.I) :
    DrawState p rp used bs t ∧
      wv t.mem p.I (slot p.w aXm) p.w = wv s.mem p.I (slot p.w aXm) p.w ∧
      (∀ j < 32, j ≠ oStatus → word t.mem p.O (8 * j) = word s.mem p.O (8 * j)) ∧
      DrawFrame p s.mem t.mem := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  have hf : Frm p.O [(8 * oStatus, 8)] s.mem t.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have hw : ∀ d, d + 8 ≤ p.IZ → word t.mem p.I d = word s.mem p.I d :=
    outer_words hf (by simp [oStatus]) (by omega_using [p.space_bounds.2.2, hz64])
  have hh : ∀ j < 32, j ≠ oStatus → word t.mem p.O (8 * j) = word s.mem p.O (8 * j) := by
    intro j hj hne
    rw [hm]
    exact hdrStore_hdr _ _ _ (by decide) hj (Ne.symm hne)
  have hf' : DrawFrame p s.mem t.mem := DrawFrame.of_scr (InScr.of_frm hf (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    change 160 ≤ p.Z
    omega_using [p.space_bounds.1]))
  refine ⟨h.transport (h.ready.of_words p.dims hw k.2.2 hdi)
    ((hw (8 * VG.Impl.Rsa.X86_64.Crt.sLink) p.space_bounds.2.1).trans h.link) hh hf' k,
    ?_, hh, hf'⟩
  exact wv_congr fun i hi => hw _ (by
    have hb := slot_le (w := p.w) (show aXm < 8 by decide)
    omega_using [hb, p.dims.z, hi])

/-- Round counters and status live beyond every tape and argument slot. -/
theorem DrawState.outer_frame {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s t : State}
    {regs : List Reg} {rs : List (Nat × Nat)} (h : DrawState p rp used bs s)
    (hf : Frm p.O rs s.mem t.mem) (hlo : ∀ r ∈ rs, 136 ≤ r.1) (hhi : ∀ r ∈ rs, r.1 + r.2 ≤ 256)
    (k : Keep regs s t) (hdi : t.gpr .rdi = p.I) : DrawState p rp used bs t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  have hw := outer_words (Z := p.IZ) hf hhi (by omega_using [p.space_bounds.2.2, hz64])
  have hh : ∀ j < 17, word t.mem p.O (8 * j) = word s.mem p.O (8 * j) := by
    intro j hj
    exact hf.word_eq (fun r hr => Or.inl (by have := hlo r hr; omega_using [this, hj])) (by omega)
  have hframe : DrawFrame p s.mem t.mem := DrawFrame.of_scr
    (InScr.of_frm hf (fun r hr => Nat.le_trans (hhi r hr) p.space_bounds.1))
  exact ⟨h.scr.congr k.2.2, h.ready.of_words p.dims hw k.2.2 hdi,
    (hw (8 * VG.Impl.Rsa.X86_64.Crt.sLink) p.space_bounds.2.1).trans h.link,
    (hh _ (by decide)).trans h.outPtr, (hh _ (by decide)).trans h.bits, (hh _ (by decide)).trans h.len,
    (hh _ (by decide)).trans h.ptr, (hh _ (by decide)).trans h.left, (hh _ (by decide)).trans h.usedWord,
    h.countBound, h.source_frame hframe k,
    ⟨fun i hi => by rw [k.2.2]; exact h.out.wr i hi, h.out.sep⟩, h.apart⟩

/-- Reassemble the invariant after a sampled prefix, including the exact
remaining slice and cumulative consumed count. -/
theorem DrawState.after_sample {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s t : State}
    {regs : List Reg} (h : DrawState p rp used bs s) (havail : p.len ≤ bs.length)
    (hr : ModulusReady t p.I p.IZ p.w p.mi p.N)
    (hl : word t.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O)
    (hh : ∀ j < 32, j ≠ oStatus → word t.mem p.O (8 * j) =
      word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j))
    (hf : DrawFrame p s.mem t.mem) (k : Keep regs s t) :
    DrawState p (off rp p.len) (used + p.len) (bs.drop p.len) t := by
  have hfadv := advanceMem_frame s.mem p.O rp p.len bs.length used
  have hstatic : ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 →
      word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j) = word s.mem p.O (8 * j) := by
    intro j hj h12 h13 h14
    apply hfadv.word_eq
    · intro r hr'
      simp only [List.mem_singleton] at hr'
      subst hr'
      change 8 * j + 8 ≤ 96 ∨ 120 ≤ 8 * j
      omega_using [h12, h13, h14]
    · omega
  refine ⟨h.scr.congr k.2.2, hr, hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨fun i hi => by rw [k.2.2]; exact h.out.wr i hi, h.out.sep⟩, ?_⟩
  · rw [hh oOut (by decide) (by decide), hstatic oOut (by decide) (by decide) (by decide) (by decide)]
    exact h.outPtr
  · rw [hh oWitnessBits (by decide) (by decide), hstatic oWitnessBits (by decide) (by decide) (by decide) (by decide)]
    exact h.bits
  · rw [hh oWitnessLen (by decide) (by decide), hstatic oWitnessLen (by decide) (by decide) (by decide) (by decide)]
    exact h.len
  · rw [hh oRandPtr (by decide) (by decide)]; exact advanceMem_ptr _ _ _ _ _ _
  · rw [hh oRandLeft (by decide) (by decide), List.length_drop]; exact advanceMem_left _ _ _ _ _ _
  · rw [hh oUsed (by decide) (by decide)]; exact advanceMem_used _ _ _ _ _ _
  · rw [List.length_drop]
    omega_using [h.countBound, havail]
  · exact source_drop (h.source_frame hf k) p.len
  · simpa only [List.length_drop] using apart_drop_right h.apart p.len

end VG.Proof.Ffdh.X86_64.ParameterCandidate
