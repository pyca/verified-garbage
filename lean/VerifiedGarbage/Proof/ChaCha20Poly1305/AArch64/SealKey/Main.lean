module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Key
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Kernel
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.PadRest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ChaCha20-Poly1305 on AArch64: `seal` from 513 to 704 bytes

`SealKey.sealMain`: the one-time key and the keystream of the data's first
448 bytes from the stream (`OpenKey.keyed_ok`); the additional data and the
lengths block; the first 448 bytes encrypted; the counter set to 8, and the
four blocks after the first eight computed into `ctx[128, 384)` while those
448 bytes are absorbed (`TailO.kernel_ok`, up to three blocks after each
double round); the rest encrypted and absorbed with its padding; the
lengths absorbed and `ctx[768, 1280)` zeroed again.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.SealKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.SealKey
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_subImm wp_mov wp_movz wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (Rk)
open VG.Proof.ChaCha20Poly1305.AArch64.TailO (loadAt_ok out_ok kernel_ok)
open VG.Proof.ChaCha20Poly1305.AArch64.OpenKey (keyed_ok ks8 ks8_eq ks_hi set12_initState8 eight32)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (kpAt kp')
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

/-- `pre`: the counter set to 8, the kernel's arguments, the length in `x2`,
and 448 in `x23`. -/
theorem pre_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv0 s₀ s) :
    WP isa (.block SealKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧ s'.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9, .x23] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.v = s.v := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  have core : WP isa (.block SealKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧ s'.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9, .x23] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_mov fun s₅ u₅ =>
      wp_movz fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, eight32]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide)]
    · rw [u₆.gpr]; exact setWidth_ofNat16 (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h2, h3, h9, h23⟩ := hr
      rw [u₆.other _ h23, u₅.other _ h2, u₄.other _ h3, u₃.other _ h0, g₂.gpr, u₁.other _ h9]
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) core)
    fun s' ⟨⟨hm, h0, h3, h2, h23, hg, hrd, hwr⟩, hv, hsp, _, _⟩ => ⟨hm, h0, h3, h2, h23, hg, hrd, hwr, hsp, hv⟩

theorem sealMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hlo : 513 ≤ L s₀) (hhi : L s₀ ≤ 704) : WP isa (SealKey.sealMain v.callee) s₀ (MainS s₀) := by
  have hLt : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hLt
  have wd := hp.wrap_d
  have oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  unfold SealKey.sealMain
  refine keyed_ok v hp fun s₁ ⟨h₁, ks₁, v₁⟩ => ?_
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  -- The additional data, and the lengths block.
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  have R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  have ks₃ : ∀ k < 512, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k := fun k hk => by
    rw [k₃.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hk,
      k₂.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hk, ks₁ k hk]
  have d₃ : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by
    rw [data_frame k₃.frame (by rdisj_all) hk, data_frame k₂.frame (by rdisj_all) hk,
      data_frame h₁.fine (by rdisj_all) hk]
  -- The data's first 448 bytes encrypted with their keystream at `ctx + 832`.
  unfold OpenKey.xorFirst
  refine WP.seq (WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x14 = s₃.gpr .x23 ∧ u.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .x14 → r ≠ .x23 → u.gpr r = s₃.gpr r) ∧ u.mem = s₃.mem)
    (wp_mov fun t₁ u₁ => wp_movz fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; exact setWidth_ofNat16 (by decide),
        fun r h14 h23 => by rw [u₂.other _ h23, u₁.other _ h14], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₄ ⟨⟨x14₄, x23₄, g₄, m₄⟩, vv₄, sp₄, rd₄, wr₄⟩ => ?_))
  have x21₄ : s₄.gpr .x21 = cx s₀ := by rw [g₄ _ (by decide) (by decide), i₃.x21]
  have x22₄ : s₄.gpr .x22 = dp s₀ + BitVec.ofNat 64 0 := by
    rw [g₄ _ (by decide) (by decide), i₃.x22, BitVec.add_zero]
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsFromAt_ok hp (k := 832) (o := 0) (n := 448)
    (by omega) (by omega) x21₄ x22₄ x23₄ (by rw [rd₄, i₃.rd]) (by rw [wr₄, i₃.wr])) (by lit_decide))
    fun s₅ ⟨⟨k₅, e₅, f₅, g₅⟩, v₅⟩ => ?_)
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x23 = s₅.gpr .x14 ∧ (∀ r, r ≠ .x23 → u.gpr r = s₅.gpr r) ∧ u.mem = s₅.mem)
    (wp_mov fun t₁ u₁ => WP.block_nil ⟨u₁.gpr, fun r h23 => u₁.other _ h23, u₁.mem⟩)).mono
    fun s₆ ⟨⟨x23₆, g₆, m₆⟩, vv₆, sp₆, rd₆, wr₆⟩ => ?_
  have g₅' (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12)
      (h13 : r ≠ .x13) : s₅.gpr r = s₄.gpr r :=
    g₅ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13⟩)
  have to₃ (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12)
      (h13 : r ≠ .x13) (h14 : r ≠ .x14) (h23 : r ≠ .x23) : s₆.gpr r = s₃.gpr r := by
    rw [g₆ r h23, g₅' r h9 h10 h11 h12 h13, g₄ r h14 h23]
  have x23₆' : s₆.gpr .x23 = BitVec.ofNat 64 (L s₀) := by
    rw [x23₆, g₅' _ (by decide) (by decide) (by decide) (by decide) (by decide), x14₄, i₃.x23, hL]
  have sp₆' : s₆.sp = s₀.sp := by rw [sp₆, k₅.sp, sp₄, i₃.sp]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, k₅.rd, rd₄, i₃.rd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, k₅.wr, wr₄, i₃.wr]
  have i₆ : Inv0 s₀ s₆ := by
    refine ⟨by rw [to₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        i₃.x21], fun r hr => ?_, sp₆', rd₆', wr₆', ?_, ?_⟩
    · have hu : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x23 := by
        simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [to₃ r hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1 hu.2.2.2.2.2.1 hu.2.2.2.2.2.2, i₃.un r hr]
    · rw [m₆]
      exact i₃.saved.frame (by rw [← m₄]; exact k₅.frame) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
    · rw [m₆]
      exact i₃.frame.trans ((by rw [← m₄]; exact k₅.frame : Frame [dR s₀] s₃.mem s₅.mem).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩)
  -- The data at `s₆`: its first 448 bytes encrypted, the rest as it was.
  have ksA : ∀ i < 448, s₄.mem (kpAt s₀ 832 + BitVec.ofNat 64 i) = (KS1 s₀).getD i 0 := by
    intro i hi
    have e : kpAt s₀ 832 + BitVec.ofNat 64 i = off (cx s₀) 768 + BitVec.ofNat 64 (64 + i) := by
      simp only [kpAt]; rw [oo, oo]; congr 1; omega
    rw [e, m₄, ks₃ _ (by omega), ks8_eq s₀ (n := L s₀) (by omega) hi]
  have c₆ : ∀ i < L s₀, s₆.mem (dp s₀ + BitVec.ofNat 64 i) =
      if i < 448 then s₀.mem (dp s₀ + BitVec.ofNat 64 i) ^^^ (KS1 s₀).getD i 0
      else s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
    intro i hi
    rw [m₆]
    split
    · next h448 =>
      have x := e₅ i h448
      simp only [Nat.zero_add] at x
      rw [x, ksA i h448, m₄, d₃ i hi]
    · next h448 =>
      have nf : ¬ (⟨dp s₀ + BitVec.ofNat 64 0, 448⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
        simp only [Region.Contains]
        rw [Offset.sub_toNat' _ (by omega) (by omega)]
        split <;> omega
      rw [f₅ _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact nf), m₄, d₃ i hi]
  have st₆ : stateAt s₆.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [m₆, stateAt_frame k₅.frame (by rdisj_all), m₄, st₃]
  have R₆ : Repr s₆.mem (off (cx s₀) 448) (otk s₀)
      ([] ++ (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))) := by
    rw [m₆]; exact Repr.frame k₅.frame (by rdisj_all) (by rw [m₄]; exact R₃)
  -- The counter set to 8, the kernel's arguments, and 448 bytes to absorb.
  refine WP.seq (WP.block_append (WP.mono (pre_ok hp i₆)
    fun s₇ ⟨m₇, x0₇, x3₇, x2₇, x23₇, g₇, rd₇, wr₇, sp₇, vv₇⟩ => ?_))
  have F₇ : Frame [sub s₀ 64 64] s₆.mem s₇.mem := by
    rw [m₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have st₇ : stateAt s₇.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
    rw [m₇, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, st₆, set12_initState8]
  have R₇ := Repr.frame F₇ (by rdisj_all) R₆
  have x21₇ : s₇.gpr .x21 = cx s₀ := by rw [g₇ _ (by decide), i₆.x21]
  have rd₇' : s₇.rd = s₀.rd := by rw [rd₇, i₆.rd]
  have wr₇' : s₇.wr = s₀.wr := by rw [wr₇, i₆.wr]
  -- The accumulator and the clamped key.
  refine (loadAt_ok hp (n := 448) (by omega) x21₇ rd₇' wr₇' x0₇ x23₇ R₇).mono
    fun s₈ ⟨a₈, x20₈, x8₈, x7₈, x6₈, m₈, g₈, vv₈, sp₈, rd₈, wr₈⟩ => ?_
  have rd₈' : s₈.rd = s₀.rd := by rw [rd₈, rd₇']
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇']
  have x0₈ : s₈.gpr .x0 = off (cx s₀) 64 := by rw [g₈ _ (by decide), x0₇]
  have x3₈ : s₈.gpr .x3 = off (cx s₀) 128 := by rw [g₈ _ (by decide), x3₇]
  have x22₇ : s₇.gpr .x22 = dp s₀ := by
    rw [g₇ _ (by decide), to₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), i₃.x22]
  have hin : ∀ k : Fin 16, InRegions (s₈.rd ++ s₈.wr) (s₈.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₈, oo, rd₈', wr₈']; exact hp.in_ctx' (by omega)
  have hw : ∀ d, d + 16 ≤ 256 → InRegions s₈.wr (s₈.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₈, oo, wr₈']; exact hp.in_ctx (by omega)
  have hst : (⟨s₈.gpr .x0, 64⟩ : Region).Disjoint ⟨s₈.gpr .x3, 256⟩ := by
    rw [x0₈, x3₈]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hrd : Readable (dp s₀) (16 * (448 / 16)) s₈ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₈', wr₈']
      exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [rd₈', wr₈', x0₈, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₈', wr₈', x0₈, oo]; exact hp.in_ctx' (by lit_omega)
  -- The kernel: the keystream of counters 8 to 11, with the first 448 bytes absorbed.
  refine WP.seq ((WP.preservedV (kernel_ok v.callee.sve 3 (c := 448 / 16) (by omega)
      (by rw [x20₈, x22₇]) x6₈ hin hw hst hrd a₈ (by omega)) (by cases v.callee.sve <;> lit_decide)).mono
    fun s₉ ⟨⟨ks₉, f₉, hv₉, h2₉, x20₉, g₉, rd₉, wr₉, sp₉⟩, v₉⟩ => ?_)
  rw [x3₈, x0₈] at ks₉
  rw [x3₈] at f₉
  have g₉' (r : Reg) (h1 : r ≠ .x1) (h4 : r ≠ .x4) (h6 : r ≠ .x6) (hp' : r ∉ Poly.regs) :
      s₉.gpr r = s₈.gpr r :=
    g₉ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h6⟩) hp'
  have x0₉ : s₉.gpr .x0 = off (cx s₀) 64 := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), x0₈]
  -- The accumulator stored, and `x22`, `x23` the rest.
  refine WP.seq ((out_ok hp x0₉ (by rw [rd₉, rd₈']) (by rw [wr₉, wr₈'])).mono
    fun s₁₀ ⟨acc₁₀, f₁₀, x21₁₀, x27₁₀, x28₁₀, x22₁₀, x23₁₀, x20₁₀, x24₁₀, x25₁₀, g₁₀, rd₁₀, wr₁₀, sp₁₀, vv₁₀⟩ => ?_)
  have x7₉ : s₉.gpr .x7 = dp s₀ := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide), x7₈, x22₇]
  have x2₉ : s₉.gpr .x2 = BitVec.ofNat 64 (L s₀) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide), g₈ _ (by decide), x2₇, x23₆']
  have x22₁₀' : s₁₀.gpr .x22 = dp s₀ + BitVec.ofNat 64 448 := by rw [x22₁₀, x20₉]
  have x23₁₀' : s₁₀.gpr .x23 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [x23₁₀, x7₉, x2₉, x20₉, VG.Offset.add_sub_add_left, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat (by omega)]
  -- Frames of the context from `s₆` to `s₁₀`.
  let tgt := [sub s₀ 32 16, sub s₀ 64 408]
  have c408 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, by simp [tgt], sub_sub s₀ h₁ (by omega) (by lit_omega)⟩
  have Fp : Frame tgt s₆.mem s₇.mem := F₇.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 64 64 (by decide) (by decide)
  have Fm : Frame tgt s₇.mem s₈.mem := by
    rw [m₈]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c408 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  have Fk : Frame tgt s₈.mem s₉.mem := f₉.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 128 256 (by decide) (by decide)
  have Fo : Frame tgt s₉.mem s₁₀.mem := f₁₀.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 448 24 (by decide) (by decide)
  have F₁₀ : Frame tgt s₆.mem s₁₀.mem := Fp.trans (Fm.trans (Fk.trans Fo))
  have dctx : ∀ i < L s₀, s₁₀.mem (dp s₀ + BitVec.ofNat 64 i) = s₆.mem (dp s₀ + BitVec.ofNat 64 i) :=
    fun i hi => data_frame F₁₀ (fun r hr => by
      simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hi
  -- The Poly1305 state after `out`: the additional data and the first 448 bytes encrypted.
  let M := [] ++ (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))
  have hml : M.length % 16 = 0 := R₆.1
  -- Bytes of the data from memories that agree on it.
  have dat : ∀ {m m' : Mem}, (∀ k < L s₀, m' (dp s₀ + BitVec.ofNat 64 k) = m (dp s₀ + BitVec.ofNat 64 k)) →
      ∀ a n, a + n ≤ L s₀ → bytesAt m' (dp s₀ + BitVec.ofNat 64 a) n = bytesAt m (dp s₀ + BitVec.ofNat 64 a) n := by
    intro m m' hm a n han
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hm _ (by omega)
  have b₈ : bytesAt s₈.mem (dp s₀) (16 * (448 / 16)) = bytesAt s₆.mem (dp s₀) 448 := by
    have := dat (m := s₆.mem) (m' := s₈.mem) (fun k hk => data_frame (Fp.trans Fm) (fun r hr => by
      simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk) 0 448 (by omega)
    rwa [BitVec.add_zero] at this
  have R₁₀ : Repr s₁₀.mem (off (cx s₀) 448) (otk s₀) (M ++ bytesAt s₆.mem (dp s₀) 448) := by
    have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    refine ⟨by rw [List.length_append, Poly1305.length_bytesAt]; omega, ?_, ?_⟩
    · have e := R₆.2.1
      rw [k24] at e ⊢
      rw [bytesAt_frame F₁₀ (fun r hr => by
          simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega)]
      exact e
    · have hlt := Poly1305.accumulate_lt (Rk (otk s₀)) M
      rw [acc₁₀ h2₉, show hacc s₉ = Poly.hval s₉ from rfl, hv₉,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₈]
      exact (Poly1305.accumulate_append hml).symm
  -- The rest encrypted with its keystream at `ctx + 128`.
  have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈']
  have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈']
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsAt_ok hp (o := 448) (n := L s₀ - 448) (by omega)
    (by omega) x21₁₀ x22₁₀' x23₁₀' rd₁₀' wr₁₀') (by lit_decide)) fun s₁₁ ⟨⟨k₁₁, e₁₁, f₁₁, g₁₁⟩, v₁₁⟩ => ?_)
  have g₁₁' (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12)
      (h13 : r ≠ .x13) : s₁₁.gpr r = s₁₀.gpr r :=
    g₁₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13⟩)
  -- The invariant.
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₉.mem.readW (off (cx s₀) d) 64 = s₈.mem.readW (off (cx s₀) d) 64 :=
    f₉.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega) (by omega) (by lit_omega)) (by decide)
  have to₁₀ (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12)
      (h13 : r ≠ .x13) : s₁₁.gpr r = s₁₀.gpr r := g₁₁' r h9 h10 h11 h12 h13
  have un₁₁ : ∀ r ∈ untouched, s₁₁.gpr r = s₀.gpr r := by
    intro r hr
    have hu := i₆.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₁₀ _ (by decide),
        g₉' _ (by decide) (by decide) (by decide) (by decide), g₈ _ (by decide), g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), x20₁₀,
        g₉' _ (by decide) (by decide) (by decide) (by decide), x8₈, g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₁₀ _ (by decide),
        g₉' _ (by decide) (by decide) (by decide) (by decide), g₈ _ (by decide), g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), x27₁₀, r32 32 (.inl rfl), m₈,
        memIn_800, g₇ _ (by decide), hu]
    · rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), x28₁₀, r32 40 (.inr rfl), m₈,
        memIn_808, g₇ _ (by decide), hu]
  let out := [sub s₀ 32 16, sub s₀ 64 408, dR s₀]
  have Fa : Frame out s₆.mem s₁₀.mem := F₁₀.sub fun r hr => by
    simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 32 16, by simp [out], fun _ h => h⟩
    · exact ⟨sub s₀ 64 408, by simp [out], fun _ h => h⟩
  have Fb : Frame out s₁₀.mem s₁₁.mem := k₁₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp [out], fun _ h => h⟩
  have F : Frame out s₆.mem s₁₁.mem := Fa.trans Fb
  have i₁₁ : Inv0 s₀ s₁₁ := ⟨by rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), x21₁₀],
    un₁₁, by rw [k₁₁.sp, sp₁₀, sp₉, sp₈, sp₇, i₆.sp], by rw [k₁₁.rd, rd₁₀'], by rw [k₁₁.wr, wr₁₀'],
    i₆.saved.frame F (fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))),
    i₆.frame.trans (F.sub fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)⟩
  -- The rest absorbed with its padding, the lengths, and `ctx[768, 1280)` zeroed again.
  have x22₁₁ : s₁₁.gpr .x22 = dp s₀ + BitVec.ofNat 64 448 := by
    rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), x22₁₀']
  have x23₁₁ : s₁₁.gpr .x23 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [to₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide), x23₁₀']
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := 448) (by omega)) i₁₁.x21 i₁₁.rd i₁₁.wr x22₁₁ x23₁₁) (by lit_decide))
    fun s₁₂ ⟨⟨k₁₂, r₁₂⟩, v₁₂⟩ => ?_)
  have i₁₂ := mac_inv0 i₁₁ k₁₂
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₂) (by lit_decide))
    fun s₁₃ ⟨⟨i₁₃, k₁₃, r₁₃⟩, v₁₃⟩ => ?_)
  refine WP.mono (Pad.zero_ok hp i₁₃.x21 i₁₃.wr) fun s₁₄ ⟨k₁₄, _, v₁₄⟩ => ?_
  have i₁₄ : Inv0 s₀ s₁₄ := i₁₃.step k₁₄
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  -- The data from `s₁₁` on.
  have fin : ∀ i < L s₀, s₁₄.mem (dp s₀ + BitVec.ofNat 64 i) = s₁₁.mem (dp s₀ + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [data_frame k₁₄.frame (by rdisj_all) hi, data_frame k₁₃.frame (by rdisj_all) hi,
        data_frame k₁₂.frame (by rdisj_all) hi]
  -- The ciphertext.
  have st₈ : stateAt s₈.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
    rw [m₈, stateAt_frame (memIn_frame (s₀ := s₀) s₇.mem (s₇.gpr .x27) (s₇.gpr .x28)) (by rdisj_all), st₇]
  have ksB : ∀ j < L s₀ - 448, s₁₀.mem (kp' s₀ + BitVec.ofNat 64 j) = (KS1 s₀).getD (448 + j) 0 := by
    intro j hj
    have hj' : j < 256 := by omega
    rw [f₁₀.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
      ks₉ j hj', st₈, ks_hi s₀ (by omega)]
  have ct : ∀ i < L s₀, s₁₄.mem (dp s₀ + BitVec.ofNat 64 i) =
      s₀.mem (dp s₀ + BitVec.ofNat 64 i) ^^^ (KS1 s₀).getD i 0 := by
    intro i hi
    rw [fin i hi]
    by_cases h448 : i < 448
    · rw [f₁₁ _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_rest (P := 448) h448 (by omega)),
        dctx i hi, c₆ i hi, ite_eq_left h448]
    · have x := e₁₁ (i - 448) (by omega)
      rw [show 448 + (i - 448) = i by omega] at x
      rw [x, ksB (i - 448) (by omega), show 448 + (i - 448) = i by omega, dctx i hi, c₆ i hi, ite_eq_right h448]
  have hct : bytesAt s₁₄.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [encrypt_eq]
    apply List.ext_getElem
    · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
    · intro i h₁ h₂
      have hi : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
      have hDl : (bytesAt s₀.mem (dp s₀) (L s₀)).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
      have e1 : (bytesAt s₁₄.mem (dp s₀) (L s₀))[i] = s₁₄.mem (dp s₀ + BitVec.ofNat 64 i) := by
        simp [bytesAt]
      have e2 : ∀ h : i < (D s₀).length, (D s₀)[i] = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := fun h => by
        simp [D, bytesAt]
      have e3 : ∀ h : i < (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (D s₀).length).length,
          (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (D s₀).length)[i] = (KS1 s₀).getD i 0 :=
        fun h => by rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, D, hDl]
      rw [List.getElem_zipWith, e1, e2, e3, ct i hi]
  -- The Poly1305 state.
  have b₆ : bytesAt s₆.mem (dp s₀) 448 = bytesAt s₁₄.mem (dp s₀) 448 := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.mp hk
    rw [fin k (by omega), f₁₁ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact not_rest (P := 448) hk (by omega)),
      dctx k (by omega)]
  have R₁₁ : Repr s₁₁.mem (off (cx s₀) 448) (otk s₀) (M ++ bytesAt s₆.mem (dp s₀) 448) :=
    Repr.frame k₁₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.c_d.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by lit_omega))) R₁₀
  have R₁₂ := r₁₂ _ _ R₁₁
  rw [b₆, show bytesAt s₁₁.mem (dp s₀ + BitVec.ofNat 64 448) (L s₀ - 448) =
      bytesAt s₁₄.mem (dp s₀ + BitVec.ofNat 64 448) (L s₀ - 448) from (dat fin 448 _ (by omega)).symm,
    List.append_assoc, split_pad (m := s₁₄.mem) (p := dp s₀) (a := 448) (by decide) (by omega), hct] at R₁₂
  have L₁₂ : bytesAt s₁₂.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₁₂.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame F (by
        intro r hr; simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))) (by lit_omega), m₆,
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega), m₄, len₃]
  have R₁₄ := Repr.frame k₁₄.frame (by rdisj_all) (r₁₃ _ _ R₁₂)
  rw [L₁₂] at R₁₄
  simp only [M, hA] at R₁₄
  refine ⟨i₁₄, fun r hr => ?_, ?_, hct⟩
  · have a₁ : (s₁₀.v r).extractLsb' 0 64 = (s₉.v r).extractLsb' 0 64 := by rw [vv₁₀]
    have a₂ : (s₉.v r).extractLsb' 0 64 = (s₇.v r).extractLsb' 0 64 := by rw [← vv₈]; exact v₉ r hr
    have a₃ : (s₇.v r).extractLsb' 0 64 = (s₅.v r).extractLsb' 0 64 := by rw [vv₇, vv₆]
    have a₄ : (s₄.v r).extractLsb' 0 64 = (s₃.v r).extractLsb' 0 64 := by rw [vv₄]
    exact (v₁₄ r hr).trans ((v₁₃ r hr).trans ((v₁₂ r hr).trans ((v₁₁ r hr).trans (a₁.trans (a₂.trans
      (a₃.trans ((v₅ r hr).trans (a₄.trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))))))))
  · refine (congrArg (Repr s₁₄.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₁₄
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

end VG.Proof.ChaCha20Poly1305.AArch64.SealKey
