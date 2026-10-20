module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH exchange on x86-64: encode or mask the shared value -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (sLink leave ws)

/-- Memory may change only at the output bytes. -/
def OutFrame (p : ExP) (m m' : Mem) : Prop :=
  ∀ x, (∀ i < p.k, x ≠ p.op + BitVec.ofNat 64 i) → m' x = m x

/-- The fixed output addresses; the data and mask may remain secret. -/
def StoreRegs (p : ExP) (xb : List Byte) (s : State) : Prop :=
  s.gpr .rbx = off p.B (inner p.w + slot p.w aY) ∧ s.gpr .rsi = p.op ∧
    s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .r15 = mask (decide (p.fl xb))

theorem finBlk_ok {p : ExP} {xb : List Byte} {s : State} (h : Checked p xb s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk) s fun t =>
      StoreRegs p xb t ∧ t.mem = s.mem ∧ Keep [.r15, .rbx, .rax, .rsi, .rcx] s t := by
  obtain ⟨⟨mi, hb, hc⟩, _, hflag, _⟩ := h
  have hOut := hb.hdr (VG.Impl.Ffdh.X86_64.Domain.sOut, p.op) (by simp [ExP.headers])
  have hK := hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers])
  have hz := hb.hZ
  have hk1 := hb.k1
  have h0 := hc.lo
  have hhi := hc.hi
  have hN := hdr_lt_slot p.w 8 (show sArr aY < 32 by decide)
  have hL := hdr_lt_slot p.w 8 (show sLink < 32 by decide)
  refine WP.mono (WP.keep [.r15, .rbx, .rax, .rsi, .rcx]
    (Q := fun t => StoreRegs p xb t ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk
  xrun [StoreRegs, State.ea, hdr, ws, hdrOff, hc.rdi, hc.hdr.harr aY (by decide),
    hc.good.scr.ld hN, hc.good.scr.ld hL, hc.link,
    hb.scr.ld (d := 8 * VG.Impl.Ffdh.X86_64.Domain.sOut) (by change 8 * 22 + 8 ≤ p.Z; omega),
    hb.scr.ld (d := 8 * sK) (by change 8 * 18 + 8 ≤ p.Z; omega), hOut, hK, hflag]
  by_cases hf : p.fl xb
  · simp only [bit, mask, show decide (p.fl xb) = true from decide_eq_true hf]
    exact ⟨off_off _ _ _, by rw [ite_eq_left hf]; rfl⟩
  · simp only [bit, mask, show decide (p.fl xb) = false from decide_eq_false hf]
    exact ⟨off_off _ _ _, by rw [ite_eq_right hf]; rfl⟩

/-- The result and its range flag, after the output store and leaving the
inner workspace. -/
def OutPost (p : ExP) (xb : List Byte) (s t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.i2osp (if p.fl xb then p.z xb else 0) p.k ∧
    t.gpr .rax = bit (p.fl xb) ∧ t.gpr .rdi = p.B ∧ OutFrame p s.mem t.mem ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
    Keep (.rdi :: mmRegs) s t

theorem output_ok {p : ExP} {xb : List Byte} {s : State} (h : Checked p xb s) :
    WP isa (seqs [.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk, storeBE,
      .block [.mov .rax (.mem (hdr sF)), leave]]) s (OutPost p xb s) := by
  obtain ⟨⟨mi, hb, hc⟩, hy, hflag, hF⟩ := h
  have hn := hb.scr.nowrap
  have h0 := hc.lo
  have hhi := hc.hi
  have hY := slot_le (w := p.w) (show aY < 8 by decide)
  have hK := hb.k1
  have hK' := hb.k2
  have hw := room_k hK hb.hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hw
  have hi8 : 8 * 32 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega
  simp only [seqs]
  refine WP.seq (WP.mono (finBlk_ok ⟨⟨mi, hb, hc⟩, hy, hflag, hF⟩)
    fun u ⟨⟨hbx, hsi, hcx, h15⟩, hm, k₁⟩ => ?_)
  refine WP.seq (WP.mono (storeBE_ok (w := p.w) (hb.scr.congr k₁.2.2) hbx hsi hcx h15 (by omega) (by omega) rfl
    (by omega) (fun i hi => by rw [k₁.2.2]; exact hb.out i hi) hb.sep)
    fun v ⟨hbytes, hf, hwr, hrd, k₂⟩ => ?_)
  have hs : Outside p.B p.Z (2 ^ 64 - p.Z) u.mem v.mem := by
    intro x hx
    have hx64 : ofs p.B x < 2 ^ 64 := (x - p.B).isLt
    apply hf
    intro i hi he
    have := hb.sep i hi
    rw [← he] at this
    omega
  have hh : ∀ d, d + 8 ≤ p.Z → word v.mem p.B d = word u.mem p.B d := fun d hd =>
    hs.word (Or.inl hd) (by omega)
  have hFs : word v.mem (off p.B (inner p.w)) (8 * sF) = bit (p.fl xb) := by
    rw [word_off, hh _ (by have := hdr_lt_slot p.w 8 (show sF < 32 by decide); omega), ← word_off, hm]
    exact hF
  have hLs : word v.mem (off p.B (inner p.w)) (8 * sLink) = p.B := by
    rw [word_off, hh _ (by have := hdr_lt_slot p.w 8 (show sLink < 32 by decide); omega), ← word_off, hm]
    exact hc.link
  have hdi : v.gpr .rdi = off p.B (inner p.w) :=
    (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hc.rdi)
  have hsV : Scr v p.B p.Z := hb.scr.congr (hwr.trans k₁.2.2)
  have hsC : Scr v (off p.B (inner p.w)) (slot p.w 8) := hsV.sub (by omega) (by unfold slot hdrBytes; omega)
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.gpr .rax = bit (p.fl xb) ∧
      t.gpr .rdi = p.B ∧ t.mem = v.mem) (by
        unfold leave
        xrun [State.ea, hdr, hdrOff, hdi, hFs, hLs,
          hsC.ld (hdr_lt_slot p.w 8 (show sF < 32 by decide)),
          hsC.ld (hdr_lt_slot p.w 8 (show sLink < 32 by decide))]) rfl) fun t ⟨⟨ha, hd, hmem⟩, k₃⟩ => ?_
  refine ⟨?_, ha, hd, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · change (List.range p.k).map _ = _
    rw [hmem, hbytes, hm, ← wv_off, hy]
    by_cases hfl : p.fl xb
    · rw [ite_eq_left (decide_eq_true hfl), ite_eq_left hfl]
    · rw [ite_eq_right (fun h => hfl (of_decide_eq_true h)), ite_eq_right hfl]
  · intro x hx
    rw [hmem, hf x hx, hm]
  · intro i hi
    rw [hmem, hh _ (by omega), hm]

end VG.Proof.Ffdh.X86_64.Exchange
