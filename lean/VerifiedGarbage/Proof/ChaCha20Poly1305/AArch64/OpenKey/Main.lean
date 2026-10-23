module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Key
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Kernel
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Rest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
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
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages

/-!
# ChaCha20-Poly1305 on AArch64: `open` from 513 to 704 bytes

`OpenKey.openMain`: the one-time key and the keystream of the data's first
448 bytes from the stream (`keyed_ok`); the additional data and the lengths
block; the counter set to 8, and the four blocks after the first eight
computed into `ctx[128, 384)` while the data's whole blocks are absorbed
(`TailO.kernel_ok`, up to five after each double round); the data's last
partial block absorbed; the data XORed with the two keystreams; the
lengths absorbed, `ctx[768, 1280)` zeroed again, and the tag computed.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.OpenKey
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_subImm wp_mov wp_movz wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (Rk)
open VG.Proof.ChaCha20Poly1305.AArch64.TailO (loadAt_ok out_ok moves_ok kernel_ok)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (kpAt kp')
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

theorem eight32 : ((((8 : BitVec 16).setWidth 32).setWidth 64).setWidth 32 : BitVec 32) = 8 := rfl

theorem set12_initState8 (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 8 = Spec.ChaCha20.initState key 8 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

/-- The keystream of the blocks after the first eight continues the one from
counter 1. -/
theorem ks_hi (s₀ : State) {k : Nat} (hk : 448 + k < L s₀) :
    (serialize (block (ctr (Spec.ChaCha20.initState (K s₀) 8 (N s₀)) (k / 64)))).getD (k % 64) 0 =
      (KS1 s₀).getD (448 + k) 0 := by
  rw [KS1, VG.Proof.ChaCha20.keystream_getD _ hk, show (448 + k) / 64 = 7 + k / 64 by omega,
    show (448 + k) % 64 = k % 64 by omega, VG.Proof.ChaCha20Poly1305.ctr_initState,
    VG.Proof.ChaCha20Poly1305.ctr_initState]
  congr 4
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  rfl

/-- `pre`: the counter set to 8, and the kernel's arguments. -/
theorem pre_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block OpenKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9] → s'.gpr r = s.gpr r) ∧ Kept [sub s₀ 64 64] s s' ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  have core : WP isa (.block OpenKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_mov fun s₅ u₅ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
    · rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, eight32]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h2, h3, h9⟩ := hr
      rw [u₅.other _ h2, u₄.other _ h3, u₃.other _ h0, g₂.gpr, u₁.other _ h9]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.preservedV (WP.kept core (by simp [OpenKey.pre, mov, clobbers, dstOf, preserved])) (by lit_decide))
    fun s' ⟨⟨⟨hm, h0, h3, h2, hg', hrd, hwr⟩, hg, hsp⟩, hv⟩ => ⟨hm, h0, h3, h2, hg', Kept.of hg hsp hrd hwr ?_, hv⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

theorem openMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hlo : 513 ≤ L s₀) (hhi : L s₀ ≤ 704) : WP isa (OpenKey.openMain v.callee) s₀ (MainO s₀) := by
  have hLt : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hLt
  have wd := hp.wrap_d
  have oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  unfold OpenKey.openMain
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
  -- The data, as it was, until it is XORed.
  have dat : ∀ {m : Mem}, (∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k)) →
      ∀ a n, a + n ≤ L s₀ → bytesAt m (dp s₀ + BitVec.ofNat 64 a) n = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 a) n := by
    intro m hm a n han
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hm _ (by omega)
  have d₃ : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by
    rw [data_frame k₃.frame (by rdisj_all) hk, data_frame k₂.frame (by rdisj_all) hk,
      data_frame h₁.fine (by rdisj_all) hk]
  -- The counter set to 8, and the kernel's arguments.
  refine WP.seq (WP.block_append (WP.mono (pre_ok hp i₃) fun s₄ ⟨m₄, x0₄, x3₄, x2₄, g₄, k₄, v₄⟩ => ?_))
  have st₄ : stateAt s₄.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
    rw [m₄, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, st₃, set12_initState8]
  have R₄ := Repr.frame k₄.frame (by rdisj_all) R₃
  have x21₄ : s₄.gpr .x21 = cx s₀ := by rw [g₄ _ (by decide), i₃.x21]
  have rd₄ : s₄.rd = s₀.rd := by rw [k₄.rd, i₃.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [k₄.wr, i₃.wr]
  have x23₄ : s₄.gpr .x23 = BitVec.ofNat 64 (L s₀) := by rw [g₄ _ (by decide), i₃.x23, hL]
  have d₄ : ∀ k < L s₀, s₄.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by
    rw [data_frame k₄.frame (by rdisj_all) hk, d₃ k hk]
  -- The accumulator and the clamped key.
  refine (loadAt_ok hp hLt x21₄ rd₄ wr₄ x0₄ x23₄ R₄).mono
    fun s₅ ⟨a₅, x20₅, x8₅, x7₅, x6₅, m₅, g₅, vv₅, sp₅, rd₅, wr₅⟩ => ?_
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄]
  have x0₅ : s₅.gpr .x0 = off (cx s₀) 64 := by rw [g₅ _ (by decide), x0₄]
  have x3₅ : s₅.gpr .x3 = off (cx s₀) 128 := by rw [g₅ _ (by decide), x3₄]
  have x22₄ : s₄.gpr .x22 = dp s₀ := by rw [g₄ _ (by decide), i₃.x22]
  have hin : ∀ k : Fin 16, InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₅, oo, rd₅', wr₅']; exact hp.in_ctx' (by omega)
  have hw : ∀ d, d + 16 ≤ 256 → InRegions s₅.wr (s₅.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₅, oo, wr₅']; exact hp.in_ctx (by omega)
  have hst : (⟨s₅.gpr .x0, 64⟩ : Region).Disjoint ⟨s₅.gpr .x3, 256⟩ := by
    rw [x0₅, x3₅]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hc16 : 16 * (L s₀ / 16) ≤ L s₀ := Nat.mul_div_le _ _
  have hrd : Readable (dp s₀) (16 * (L s₀ / 16)) s₅ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₅', wr₅']
      exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [rd₅', wr₅', x0₅, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₅', wr₅', x0₅, oo]; exact hp.in_ctx' (by lit_omega)
  -- The kernel: the keystream of counters 8 to 11, with the data's whole blocks absorbed.
  refine WP.seq ((WP.preservedV (kernel_ok v.callee.sve 5 (c := L s₀ / 16) (by omega)
      (by rw [x20₅, x22₄]) x6₅ hin hw hst hrd a₅ (by omega)) (by cases v.callee.sve <;> lit_decide)).mono
    fun s₆ ⟨⟨ks₆, f₆, hv₆, h2₆, x20₆, g₆, rd₆, wr₆, sp₆⟩, v₆⟩ => ?_)
  rw [x3₅, x0₅] at ks₆
  rw [x3₅] at f₆
  have g₆' (r : Reg) (h1 : r ≠ .x1) (h4 : r ≠ .x4) (h6 : r ≠ .x6) (hp' : r ∉ Poly.regs) :
      s₆.gpr r = s₅.gpr r :=
    g₆ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h6⟩) hp'
  have x0₆ : s₆.gpr .x0 = off (cx s₀) 64 := by
    rw [g₆' _ (by decide) (by decide) (by decide) (by decide), x0₅]
  -- The accumulator stored.
  refine WP.seq ((out_ok hp x0₆ (by rw [rd₆, rd₅']) (by rw [wr₆, wr₅'])).mono
    fun s₇ ⟨acc₇, f₇, x21₇, x27₇, x28₇, x22₇, x23₇, x20₇, x24₇, x25₇, g₇, rd₇, wr₇, sp₇, vv₇⟩ => ?_)
  have x7₆ : s₆.gpr .x7 = dp s₀ := by rw [g₆' _ (by decide) (by decide) (by decide) (by decide), x7₅, x22₄]
  have x2₆ : s₆.gpr .x2 = BitVec.ofNat 64 (L s₀) := by
    rw [g₆' _ (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide), x2₄, i₃.x23, hL]
  have x22₇' : s₇.gpr .x22 = dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16)) := by rw [x22₇, x20₆]
  have x23₇' : s₇.gpr .x23 = BitVec.ofNat 64 (L s₀ - 16 * (L s₀ / 16)) := by
    rw [x23₇, x7₆, x2₆, x20₆, VG.Offset.add_sub_add_left, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hc16]
  -- The data until the XOR.
  have d₇ : ∀ k < L s₀, s₇.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [data_frame (s₀ := s₀) f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk,
      data_frame (s₀ := s₀) f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk, m₅,
      data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28))
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk, d₄ k hk]
  have b₅ : bytesAt s₅.mem (dp s₀) (16 * (L s₀ / 16)) = bytesAt s₀.mem (dp s₀) (16 * (L s₀ / 16)) := by
    have := dat (m := s₅.mem) (fun k hk => by
      rw [m₅, data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28))
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk, d₄ k hk]) 0 (16 * (L s₀ / 16))
      (by omega)
    rwa [BitVec.add_zero] at this
  -- The Poly1305 state after `out`: the additional data and the data's whole blocks.
  let M := [] ++ (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))
  have hml : M.length % 16 = 0 := R₄.1
  let tgt := [sub s₀ 32 16, sub s₀ 64 408]
  have c408 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, by simp [tgt], sub_sub s₀ h₁ (by omega) (by lit_omega)⟩
  have Fm : Frame tgt s₄.mem s₅.mem := by
    rw [m₅]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c408 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  have Fk : Frame tgt s₅.mem s₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 128 256 (by decide) (by decide)
  have Fo : Frame tgt s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 448 24 (by decide) (by decide)
  have F₇ : Frame tgt s₄.mem s₇.mem := Fm.trans (Fk.trans Fo)
  have R₇ : Repr s₇.mem (off (cx s₀) 448) (otk s₀) (M ++ bytesAt s₀.mem (dp s₀) (16 * (L s₀ / 16))) := by
    have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    refine ⟨by rw [List.length_append, Poly1305.length_bytesAt]; omega, ?_, ?_⟩
    · have e := R₄.2.1
      rw [k24] at e ⊢
      rw [bytesAt_frame F₇ (fun r hr => by
          simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega)]
      exact e
    · have hlt := Poly1305.accumulate_lt (Rk (otk s₀)) M
      rw [acc₇ h2₆, show hacc s₆ = Poly.hval s₆ from rfl, hv₆,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₅]
      exact (Poly1305.accumulate_append hml).symm
  -- The last partial block, absorbed with its padding.
  have rd₇' : s₇.rd = s₀.rd := by rw [rd₇, rd₆, rd₅']
  have wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆, wr₅']
  have hsrc := srcAt hp (p := 16 * (L s₀ / 16)) hc16
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ hsrc
    x21₇ rd₇' wr₇' x22₇' x23₇') (by lit_decide)) fun s₈ ⟨⟨k₈, r₈⟩, v₈⟩ => ?_)
  have R₈ := r₈ _ _ R₇
  -- The data, back in `x22` and `x23`.
  refine WP.seq (moves_ok.mono fun s₉ ⟨⟨x22₉, x23₉, g₉, m₉⟩, vv₉, sp₉, rd₉, wr₉⟩ => ?_)
  have x24₈ : s₈.gpr .x24 = dp s₀ := by rw [k₈.cs _ (pres .x24) (pres30 .x24), x24₇, x7₆]
  have x25₈ : s₈.gpr .x25 = BitVec.ofNat 64 (L s₀) := by rw [k₈.cs _ (pres .x25) (pres30 .x25), x25₇, x2₆]
  have x21₉ : s₉.gpr .x21 = cx s₀ := by
    rw [g₉ _ (by decide) (by decide), k₈.cs _ (pres .x21) (pres30 .x21), x21₇]
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, k₈.rd, rd₇']
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, k₈.wr, wr₇']
  have d₉ : ∀ k < L s₀, s₉.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m₉, data_frame (s₀ := s₀) k₈.frame (fun r hr => by
      simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk, d₇ k hk]
  -- The data's first 448 bytes XORed with their keystream at `ctx + 832`.
  unfold xorFirst
  refine WP.seq (WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x14 = s₉.gpr .x23 ∧ u.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .x14 → r ≠ .x23 → u.gpr r = s₉.gpr r) ∧ u.mem = s₉.mem)
    (wp_mov fun t₁ u₁ => wp_movz fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; exact setWidth_ofNat16 (by decide),
        fun r h14 h23 => by rw [u₂.other _ h23, u₁.other _ h14], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₁₀ ⟨⟨x14₁₀, x23₁₀, g₁₀, m₁₀⟩, vv₁₀, sp₁₀, rd₁₀, wr₁₀⟩ => ?_))
  have x21₁₀ : s₁₀.gpr .x21 = cx s₀ := by rw [g₁₀ _ (by decide) (by decide), x21₉]
  have x22₁₀ : s₁₀.gpr .x22 = dp s₀ + BitVec.ofNat 64 0 := by
    rw [g₁₀ _ (by decide) (by decide), x22₉, x24₈, BitVec.add_zero]
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsFromAt_ok hp (k := 832) (o := 0) (n := 448)
    (by omega) (by omega) x21₁₀ x22₁₀ x23₁₀ (by rw [rd₁₀, rd₉']) (by rw [wr₁₀, wr₉'])) (by lit_decide))
    fun s₁₁ ⟨⟨k₁₁, e₁₁, f₁₁, g₁₁⟩, v₁₁⟩ => ?_)
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x23 = s₁₁.gpr .x14 ∧ (∀ r, r ≠ .x23 → u.gpr r = s₁₁.gpr r) ∧ u.mem = s₁₁.mem)
    (wp_mov fun t₁ u₁ => WP.block_nil ⟨u₁.gpr, fun r h23 => u₁.other _ h23, u₁.mem⟩)).mono
    fun s₁₂ ⟨⟨x23₁₂, g₁₂, m₁₂⟩, vv₁₂, sp₁₂, rd₁₂, wr₁₂⟩ => ?_
  -- The rest of the data, after 448 bytes.
  refine WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x22 = s₁₂.gpr .x22 + BitVec.ofNat 64 448 ∧ u.gpr .x23 = s₁₂.gpr .x23 - BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → u.gpr r = s₁₂.gpr r) ∧ u.mem = s₁₂.mem)
    (wp_addImm (by decide) fun t₁ u₁ => wp_subImm (by decide) fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 => by rw [u₂.other _ h23, u₁.other _ h22], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₁₃ ⟨⟨x22₁₃, x23₁₃, g₁₃, m₁₃⟩, vv₁₃, sp₁₃, rd₁₃, wr₁₃⟩ => ?_)
  have g₁₁' (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12)
      (h13 : r ≠ .x13) : s₁₁.gpr r = s₁₀.gpr r :=
    g₁₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13⟩)
  have x21₁₃ : s₁₃.gpr .x21 = cx s₀ := by
    rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide),
      g₁₁' _ (by decide) (by decide) (by decide) (by decide) (by decide), x21₁₀]
  have x22₁₃ : s₁₃.gpr .x22 = dp s₀ + BitVec.ofNat 64 448 := by
    rw [x22₁₃, g₁₂ _ (by decide), g₁₁' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁₀ _ (by decide) (by decide), x22₉, x24₈]
  have x23₁₃ : s₁₃.gpr .x23 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [x23₁₃, x23₁₂, g₁₁' _ (by decide) (by decide) (by decide) (by decide) (by decide), x14₁₀, x23₉, x25₈,
      VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat (by omega)]
  have rd₁₃' : s₁₃.rd = s₀.rd := by rw [rd₁₃, rd₁₂, k₁₁.rd, rd₁₀, rd₉']
  have wr₁₃' : s₁₃.wr = s₀.wr := by rw [wr₁₃, wr₁₂, k₁₁.wr, wr₁₀, wr₉']
  -- The rest XORed with its keystream at `ctx + 128`.
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsAt_ok hp (o := 448) (n := L s₀ - 448) (by omega)
    (by omega) x21₁₃ x22₁₃ x23₁₃ rd₁₃' wr₁₃') (by lit_decide)) fun s₁₄ ⟨⟨k₁₄, e₁₄, f₁₄, g₁₄⟩, v₁₄⟩ => ?_)
  have g₁₄' (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12)
      (h13 : r ≠ .x13) : s₁₄.gpr r = s₁₃.gpr r :=
    g₁₄ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13⟩)
  -- Registers.
  have to₇ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h9 : r ≠ .x9) (h10 : r ≠ .x10)
      (h11 : r ≠ .x11) (h12 : r ≠ .x12) (h13 : r ≠ .x13) (h14 : r ≠ .x14) (h22 : r ≠ .x22)
      (h23 : r ≠ .x23) : s₁₄.gpr r = s₇.gpr r := by
    rw [g₁₄' r h9 h10 h11 h12 h13, g₁₃ r h22 h23, g₁₂ r h23, g₁₁' r h9 h10 h11 h12 h13, g₁₀ r h14 h23,
      g₉ r h22 h23, k₈.cs r hr h30]
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₆.mem.readW (off (cx s₀) d) 64 = s₅.mem.readW (off (cx s₀) d) 64 :=
    f₆.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega) (by omega) (by lit_omega)) (by decide)
  have un₁₄ : ∀ r ∈ untouched, s₁₄.gpr r = s₀.gpr r := by
    intro r hr
    have hu := i₃.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), g₇ _ (by decide), g₆' _ (by decide) (by decide) (by decide) (by decide),
        g₅ _ (by decide), g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), x20₇, g₆' _ (by decide) (by decide) (by decide) (by decide), x8₅,
        g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), g₇ _ (by decide), g₆' _ (by decide) (by decide) (by decide) (by decide),
        g₅ _ (by decide), g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), x27₇, r32 32 (.inl rfl), m₅, memIn_800, g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), x28₇, r32 40 (.inr rfl), m₅, memIn_808, g₄ _ (by decide), hu]
  -- The frames.
  let out := [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, dR s₀]
  have Fa : Frame out s₃.mem s₄.mem := k₄.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
  have Fb : Frame out s₄.mem s₇.mem := F₇.sub fun r hr => by
    simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 32 16, by simp [out], fun _ h => h⟩
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
  have Fc : Frame out s₇.mem s₈.mem := k₈.frame.sub fun r hr => by
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
    · exact ⟨sub s₀ 16 16, by simp [out], fun _ h => h⟩
  have Fd : Frame out s₈.mem s₁₁.mem := by
    rw [← m₉, ← m₁₀]
    exact k₁₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp [out], fun _ h => h⟩
  have Fe : Frame out s₁₁.mem s₁₄.mem := by
    rw [← m₁₂, ← m₁₃]
    exact k₁₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp [out], fun _ h => h⟩
  have F : Frame out s₃.mem s₁₄.mem := Fa.trans (Fb.trans (Fc.trans (Fd.trans Fe)))
  have sp₁₄ : s₁₄.sp = s₀.sp := by
    rw [k₁₄.sp, sp₁₃, sp₁₂, k₁₁.sp, sp₁₀, sp₉, k₈.sp, sp₇, sp₆, sp₅, k₄.sp, i₃.sp]
  have i₁₄ : Inv0 s₀ s₁₄ := ⟨by rw [g₁₄' _ (by decide) (by decide) (by decide) (by decide) (by decide), x21₁₃],
    un₁₄, sp₁₄, by rw [k₁₄.rd, rd₁₃'], by rw [k₁₄.wr, wr₁₃'],
    i₃.saved.frame F (fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))),
    i₃.frame.trans (F.sub fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)⟩
  -- The lengths, `ctx[768, 1280)` zeroed again, and the tag.
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₄) (by lit_decide))
    fun s₁₅ ⟨⟨i₁₅, k₁₅, r₁₅⟩, v₁₅⟩ => ?_)
  refine WP.seq (WP.mono (Pad.zero_ok hp i₁₅.x21 i₁₅.wr) fun s₁₆ ⟨k₁₆, _, v₁₆⟩ => ?_)
  have i₁₆ : Inv0 s₀ s₁₆ := i₁₅.step k₁₆
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine WP.mono (WP.preservedV (finalizeTo_ok0 hp i₁₆ (out := 48) (by omega)) (by lit_decide))
    fun s₁₇ ⟨⟨k₁₇, tag₁₇⟩, v₁₇⟩ => ?_
  -- The tag computed.
  have e₈ : bytesAt s₇.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ - 16 * (L s₀ / 16)) =
      bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ - 16 * (L s₀ / 16)) :=
    dat d₇ _ _ (by omega)
  rw [e₈, List.append_assoc, split_pad (m := s₀.mem) (p := dp s₀) (Nat.mul_mod_right 16 _) hc16] at R₈
  have hP : ∀ r ∈ [dR s₀], (sub s₀ 448 128).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.c_d.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by lit_omega))
  have R₁₄ : Repr s₁₄.mem (off (cx s₀) 448) (otk s₀)
      (M ++ (bytesAt s₀.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s₀.mem (dp s₀) (L s₀)))) := by
    refine Repr.frame k₁₄.frame (fun r hr => (hP r hr).symm.symm) ?_
    rw [m₁₃, m₁₂]
    refine Repr.frame k₁₁.frame (fun r hr => (hP r hr).symm.symm) ?_
    rw [m₁₀, m₉]; exact R₈
  have R₁₆ := Repr.frame k₁₆.frame (by rdisj_all) (r₁₅ _ _ R₁₄)
  have T₁₇ := tag₁₇ _ _ R₁₆
  have L₁₄ : bytesAt s₁₄.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame F (by
        intro r hr; simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))) (by lit_omega), len₃]
  rw [L₁₄] at T₁₇
  simp only [M, hA] at T₁₇
  have vec : ∀ r ∈ preservedV, (s₁₇.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 := by
    intro r hr
    have a₁ : (s₁₄.v r).extractLsb' 0 64 = (s₁₃.v r).extractLsb' 0 64 := v₁₄ r hr
    have a₂ : (s₁₃.v r).extractLsb' 0 64 = (s₁₁.v r).extractLsb' 0 64 := by rw [vv₁₃, vv₁₂]
    have a₃ : (s₁₁.v r).extractLsb' 0 64 = (s₁₀.v r).extractLsb' 0 64 := v₁₁ r hr
    have a₄ : (s₁₀.v r).extractLsb' 0 64 = (s₈.v r).extractLsb' 0 64 := by rw [vv₁₀, vv₉]
    have a₅ : (s₇.v r).extractLsb' 0 64 = (s₆.v r).extractLsb' 0 64 := by rw [vv₇]
    have a₆ : (s₅.v r).extractLsb' 0 64 = (s₄.v r).extractLsb' 0 64 := by rw [vv₅]
    exact (v₁₇ r hr).trans ((v₁₆ r hr).trans ((v₁₅ r hr).trans (a₁.trans (a₂.trans (a₃.trans (a₄.trans
      ((v₈ r hr).trans (a₅.trans ((v₆ r hr).trans (a₆.trans ((v₄ r hr).trans ((v₃ r hr).trans
      ((v₂ r hr).trans (v₁ r hr))))))))))))))
  refine ⟨i₁₆.step k₁₇ (fun r hr => ?_) (fun r hr => ?_), vec, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₁₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  -- The data decrypted.
  · have fin : ∀ i < L s₀, s₁₇.mem (dp s₀ + BitVec.ofNat 64 i) = s₁₄.mem (dp s₀ + BitVec.ofNat 64 i) :=
      fun i hi => by
        rw [data_frame k₁₇.frame (by rdisj_all) hi, data_frame k₁₆.frame (by rdisj_all) hi,
          data_frame k₁₅.frame (by rdisj_all) hi]
    -- The keystream of the first 448 bytes, from the stream.
    have ksA : ∀ i < 448, s₁₀.mem (kpAt s₀ 832 + BitVec.ofNat 64 i) = (KS1 s₀).getD i 0 := by
      intro i hi
      have e : kpAt s₀ 832 + BitVec.ofNat 64 i = off (cx s₀) 768 + BitVec.ofNat 64 (64 + i) := by
        simp only [kpAt]; rw [oo, oo]; congr 1; omega
      have h512 : 64 + i < 512 := by omega
      rw [e, m₁₀, m₉,
        k₈.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        f₇.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        f₆.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512, m₅,
        (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28)).bytes (R := sub s₀ 768 512)
          (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        k₄.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        ks₃ _ h512, ks8_eq s₀ (n := L s₀) (by omega) hi]
    -- The keystream of the rest, from the kernel.
    have st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
      rw [m₅, stateAt_frame (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28)) (by rdisj_all), st₄]
    have ksB : ∀ j < L s₀ - 448, s₁₃.mem (kp' s₀ + BitVec.ofNat 64 j) = (KS1 s₀).getD (448 + j) 0 := by
      intro j hj
      have hj' : j < 256 := by omega
      rw [m₁₃, m₁₂, k₁₁.frame.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
        m₁₀, m₉, k₈.frame.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
        f₇.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
        ks₆ j hj', st₅, ks_hi s₀ (by omega)]
    rw [bytesAt_frame k₁₇.frame (by rdisj_all) hL', bytesAt_frame k₁₆.frame (by rdisj_all) hL',
      bytesAt_frame k₁₅.frame (by rdisj_all) hL', encrypt_eq]
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
      rw [List.getElem_zipWith, e1, e2, e3]
      by_cases h448 : i < 448
      · have x := e₁₁ i h448
        simp only [Nat.zero_add] at x
        rw [f₁₄ _ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact not_rest (P := 448) h448 (by omega)),
          m₁₃, m₁₂, x, ksA i h448, m₁₀, d₉ i hi]
      · have x := e₁₄ (i - 448) (by omega)
        rw [show 448 + (i - 448) = i by omega] at x
        have nf : ¬ (⟨dp s₀ + BitVec.ofNat 64 0, 448⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 i) 1 := by
          simp only [Region.Contains]
          rw [Offset.sub_toNat' _ (by omega) (by omega)]
          split <;> omega
        rw [x, ksB (i - 448) (by omega), show 448 + (i - 448) = i by omega, m₁₃, m₁₂,
          f₁₁ _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact nf), m₁₀, d₉ i hi]

end VG.Proof.ChaCha20Poly1305.AArch64.OpenKey
