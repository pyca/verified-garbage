module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypt
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.RoundLoop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Tail
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.ChaCha20.Stream

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `cryptStitched`

From the state after the data's first `o` bytes (a multiple of 64) were
encrypted from counter 1 and absorbed, with the counter past them and `x22`,
`x23` pointing after them (`Entry`): after `T` chunks (none for fewer than
512 bytes after them), the data's first `o + 512 T` bytes encrypted from
counter 1, the counter advanced past them, the stream's arguments set to the
rest, and the bytes absorbed (`pre`) and the rest's pointer and length in
`x22`, `x23`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked Acc rebase rebase_of)
open VG.Proof.ChaCha20 (ctr)
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov wp_str32)
open VG.Proof.Poly1305 (absorbAll)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

variable {sve : Bool}

/-- The bytes absorbed after `T` chunks from byte `o`: all of them when
decrypting, all but the last chunk when encrypting. -/
def pre (o : Nat) (enc : Bool) (T : Nat) : Nat := o + if enc then 512 * (T - 1) else 512 * T

theorem pre_le (o : Nat) (enc : Bool) (T : Nat) : pre o enc T ≤ o + 512 * T := by
  cases enc <;> simp only [pre, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem pre_ge (o : Nat) (enc : Bool) (T : Nat) : o ≤ pre o enc T := Nat.le_add_right _ _

theorem pre_zero (o : Nat) (enc : Bool) : pre o enc 0 = o := by
  cases enc <;> simp [pre]

theorem pre_mod {o : Nat} (ho : o % 16 = 0) (enc : Bool) (T : Nat) : pre o enc T % 16 = 0 := by
  cases enc <;> simp only [pre, Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- The keystream from counter 1. -/
abbrev KS1 (s₀ : State) : List Byte :=
  keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)

/-- The keystream after `q` blocks continues the one from counter 1. -/
theorem ks1_off (s₀ : State) {q k : Nat} (hk : 64 * q + k < L s₀) :
    (keystream (ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) q) (L s₀ - 64 * q)).getD k 0 =
      (KS1 s₀).getD (64 * q + k) 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ (by omega), VG.Proof.ChaCha20.keystream_getD _ hk,
    VG.Proof.ChaCha20.ctr_ctr, show q + k / 64 = (64 * q + k) / 64 by omega,
    show k % 64 = (64 * q + k) % 64 by omega]

/-- What `cryptStitched` starts from: the data's first `o` bytes (a multiple
of 64) encrypted from `s` and absorbed, the counter past them, and `x22`,
`x23` the data after them. -/
structure Entry (enc : Bool) (o : Nat) (s₀ s : State) (key msg : List Byte) (w : State) : Prop where
  inv : Inv0 s₀ w
  o64 : o % 64 = 0
  le : o ≤ L s₀
  x22 : w.gpr .x22 = dp s₀ + BitVec.ofNat 64 o
  x23 : w.gpr .x23 = BitVec.ofNat 64 (L s₀ - o)
  st : stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64)
  data : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < o then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  mac : Repr w.mem (off (cx s₀) 448) key (msg ++ bytesAt (if enc then w.mem else s.mem) (dp s₀) o)
  vec : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- What `cryptStitched` leaves, after `T` chunks from byte `o`, from `s` (its
data and Poly1305's message) and `w` (the rest of memory). -/
structure Crypted (enc : Bool) (o : Nat) (s₀ s w : State) (key msg : List Byte) (T : Nat) (u : State) :
    Prop where
  inv : Inv0 s₀ u
  le : o + 512 * T ≤ L s₀
  lt : L s₀ - (o + 512 * T) < 512
  x0 : u.gpr .x0 = off (cx s₀) 64
  x1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (o + 512 * T)
  x2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - (o + 512 * T))
  x3 : u.gpr .x3 = off (cx s₀) 128
  x22 : u.gpr .x22 = dp s₀ + BitVec.ofNat 64 (pre o enc T)
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀ - pre o enc T)
  cnt : stateAt u.mem (off (cx s₀) 64) =
    ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64 + 8 * T)
  data : ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < o + 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 408, sub s₀ 32 16, dR s₀] w.mem u.mem
  mac : Repr u.mem (off (cx s₀) 448) key
    (msg ++ bytesAt (if enc then u.mem else s.mem) (dp s₀) (pre o enc T))
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-! ## Helpers -/

/-- The vector registers other than `v8` and `v9` are kept. -/
theorem WP.otherV {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true) :
    WP isa c s fun u => Q u ∧ ∀ r ∈ preservedV, r ≠ .v8 → r ≠ .v9 → u.v r = s.v r := by
  obtain ⟨t, u, he, hq⟩ := h
  exact ⟨t, u, he, hq, fun r hr h8 h9 => Exec.vec (fun i hi =>
    VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV_ne (List.all_eq_true.mp
      ((Code.allInstrs_eq _ c) ▸ hc) i hi) hr h8 h9) he⟩

theorem bulk_otherV (sve enc : Bool) :
    (Stitch.bulk sve enc).allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true := by
  cases sve <;> cases enc
  · show Stitch.bulkOpen.allInstrs _ = true; lit_decide
  · show Stitch.bulkSeal.allInstrs _ = true; lit_decide
  · show Stitch.bulkOpenSve.allInstrs _ = true; lit_decide
  · show Stitch.bulkSealSve.allInstrs _ = true; lit_decide

/-- A byte of the data outside a frame of the context. -/
theorem data_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {k : Nat} (hk : k < L s₀) :
    m' (dp s₀ + BitVec.ofNat 64 k) = m (dp s₀ + BitVec.ofNat 64 k) :=
  hf.bytes hd (Nat.le_of_lt (s₀.gpr .x5).isLt) hk

/-- The parts of the context `cryptStitched` writes, besides the stream's. -/
abbrev ctxW (s₀ : State) : List Region := [sub s₀ 64 408, sub s₀ 32 16]

theorem ctxW_data {s₀ : State} (hp : APre e s₀) : ∀ r ∈ ctxW s₀, (dR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))

theorem ctxW_sub (s₀ : State) : ∀ r ∈ ctxW s₀, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩

theorem ctxW_saved (s₀ : State) : ∀ r ∈ ctxW s₀, (sub s₀ 576 56).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)

/-- The state after `cryptSetup`. -/
theorem setup_ok {s₀ : State} {w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block cryptSetup) w fun s₂ =>
      s₂.gpr .x0 = off (cx s₀) 64 ∧ s₂.gpr .x1 = w.gpr .x22 ∧ s₂.gpr .x2 = w.gpr .x23 ∧
      s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if (w.gpr .x23).toNat < 512 then 1 else 0) ∧
      Kept [] w s₂ ∧ s₂.mem = w.mem ∧
      ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block cryptSetup) w fun s₂ =>
      s₂.gpr .x0 = off (cx s₀) 64 ∧ s₂.gpr .x1 = w.gpr .x22 ∧ s₂.gpr .x2 = w.gpr .x23 ∧
      s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if (w.gpr .x23).toNat < 512 then 1 else 0) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → s₂.gpr r = w.gpr r) ∧
      s₂.mem = w.mem ∧ s₂.rd = w.rd ∧ s₂.wr = w.wr := by
    have c₁ : WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128])
        w fun s₁ => s₁.gpr .x0 = off (cx s₀) 64 ∧ s₁.gpr .x1 = w.gpr .x22 ∧
          s₁.gpr .x2 = w.gpr .x23 ∧ s₁.gpr .x3 = off (cx s₀) 128 ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → s₁.gpr r = w.gpr r) ∧
          s₁.mem = w.mem ∧ s₁.rd = w.rd ∧ s₁.wr = w.wr :=
      wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ =>
        wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
          ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
            by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
            by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
            by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
            fun r h0 h1 h2 h3 => by rw [u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0],
            by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
            by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    refine WP.block_append (c₁.mono fun s₁ ⟨x0₁, x1₁, x2₁, x3₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.check_ok s₁).mono
      fun s₂ ⟨x5₂, g₂, m₂, rd₂, wr₂, _, _⟩ => ?_
    exact ⟨by rw [g₂ _ (by decide), x0₁], by rw [g₂ _ (by decide), x1₁], by rw [g₂ _ (by decide), x2₁],
      by rw [g₂ _ (by decide), x3₁], by rw [x5₂, x2₁],
      fun r h0 h1 h2 h3 h5 => by rw [g₂ r h5, g₁ r h0 h1 h2 h3], by rw [m₂, m₁], by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩
  refine (WP.preservedV (WP.withSp core) (by lit_decide)).mono
    fun s₂ ⟨⟨⟨x0, x1, x2, x3, x5, g, m, rd, wr⟩, sp⟩, hv⟩ => ⟨x0, x1, x2, x3, x5,
      ⟨fun r hr _ => g r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
        (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
        (by rintro rfl; exact absurd hr (by decide)), sp, rd, wr, by rw [m]; exact Frame.refl _ _⟩, m, hv⟩

/-- `counterOne`: the counter set to 1. -/
theorem counterOne_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block counterOne) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ Kept [sub s₀ 64 64] s s' ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  have core : WP isa (.block counterOne) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    exact WP.block_nil ⟨by rw [g₂.mem, u₁.gpr, u₁.mem, one32], by rw [g₂.rd, u₁.rd], by rw [g₂.wr, u₁.wr]⟩
  refine WP.mono (WP.preservedV (WP.kept core rfl) (by lit_decide))
    fun s' ⟨⟨⟨hm, hrd, hwr⟩, hg, hsp⟩, hv⟩ => ⟨hm, Kept.of hg hsp hrd hwr ?_, hv⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

/-- The ChaCha20 state after `counterOne`: counter 1. -/
theorem setup_cnt {s₀ : State} {s : State}
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    stateAt (s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32)) (off (cx s₀) 64) =
      Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
  rw [show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, hst, set12_initState]

/-- After the lengths and `counterOne`, `cryptStitched` starts from the data's
first byte. -/
theorem entry_zero (enc : Bool) {s₀ : State} {s w : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg)
    (hm : w.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32)) (hk : Kept [sub s₀ 64 64] s w) :
    Entry enc 0 s₀ w key msg w := by
  refine ⟨(h.step1 hk (by lit_omega) (by lit_omega) (by lit_omega)).inv0, by decide, Nat.zero_le _, ?_, ?_,
    ?_, fun k _ => by rw [ite_eq_right (Nat.not_lt_zero k)], ?_, fun _ _ => rfl⟩
  · rw [hk.cs _ (pres .x22) (pres30 .x22), h.x22, Poly1305.AArch64.add_ofNat_zero]
  · rw [hk.cs _ (pres .x23) (pres30 .x23), h.x23, Nat.sub_zero, hL]
  · rw [hm, setup_cnt hst, Nat.zero_div, VG.Proof.ChaCha20.ctr_zero]
  · rw [Stitch.bytesAt_zero, List.append_nil]
    exact Repr.frame hk.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr

theorem Inv0.kept {s₀ s s' : State} (h : Inv0 s₀ s) (hk : Kept [] s s') : Inv0 s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

/-- No chunks: fewer than 512 bytes from byte `o`. -/
theorem short_crypted (enc : Bool) {s₀ : State} {o : Nat} {s w : State} {key msg : List Byte}
    (E : Entry enc o s₀ s key msg w) {s₂ : State}
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = w.gpr .x22) (x2₂ : s₂.gpr .x2 = w.gpr .x23)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [] w s₂) (m₂ : s₂.mem = w.mem)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64)
    (hs : L s₀ - o < 512) :
    Crypted enc o s₀ s w key msg 0 s₂ := by
  have h22 : s₂.gpr .x22 = w.gpr .x22 := k₂.cs _ (pres .x22) (pres30 .x22)
  have h23 : s₂.gpr .x23 = w.gpr .x23 := k₂.cs _ (pres .x23) (pres30 .x23)
  refine ⟨E.inv.kept k₂, by have := E.le; omega, by omega, x0₂, ?_, ?_, x3₂, ?_, ?_, ?_, fun k hk => ?_,
    ?_, ?_, fun r hr => (v₂ r hr).trans (E.vec r hr)⟩
  · rw [x1₂, E.x22, Nat.mul_zero, Nat.add_zero]
  · rw [x2₂, E.x23, Nat.mul_zero, Nat.add_zero]
  · rw [pre_zero, h22, E.x22]
  · rw [pre_zero, h23, E.x23]
  · rw [m₂, E.st, Nat.mul_zero, Nat.add_zero]
  · rw [m₂, Nat.mul_zero, Nat.add_zero]; exact E.data k hk
  · rw [m₂]; exact Frame.refl _ _
  · rw [pre_zero, m₂]; exact E.mac

/-! ## The accumulator in registers -/

theorem h2_le {a b c : Nat} (h : a + 2 ^ 64 * b + 2 ^ 128 * c < Spec.Poly1305.P) : c ≤ 4 := by
  have h₁ : 2 ^ 128 * c < 2 ^ 128 * 5 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left h₁)

/-- The accumulator's words, from the 24 bytes. -/
theorem leNum_words (m : Mem) (c : Addr) :
    VG.Spec.Poly1305.leNum (bytesAt m (off c 448) 24) = (m.readW (off c 448) 64).toNat +
      2 ^ 64 * (m.readW (off c 456) 64).toNat + 2 ^ 128 * (m.readW (off c 464) 64).toNat := by
  rw [Poly1305.AArch64.leNum_acc]
  simp only [Poly1305.AArch64.w64, off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The key's clamped words, as `polyIn` stores them. -/
theorem clamp_words (m : Mem) (c : Addr) :
    Poly1305.AArch64.Rk m (off c 448) = (m.readW (off c 472) 64 &&& M0).toNat +
      2 ^ 64 * (m.readW (off c 480) 64 &&& M1).toNat := by
  simp only [Poly1305.AArch64.Rk, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memIn_288 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 288) 64 = m.readW (off c 472) 64 &&& M0 := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    Mem.readW_writeW_self64]

theorem memIn_296 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 296) 64 = m.readW (off c 480) 64 &&& M1 := by
  rw [memIn, Mem.readW_writeW_self64]

theorem memIn_800 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 32) 64 = a := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

theorem memIn_808 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 40) 64 = b := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

/-- The words `polyIn` stores. -/
abbrev inR (s₀ : State) : List Region := [sub s₀ 288 16, sub s₀ 32 16]

theorem memIn_frame {s₀ : State} (m : Mem) (a b : BitVec 64) :
    Frame (inR s₀) m (memIn m (cx s₀) a b) := by
  have c (k d : Nat) (h₁ : k ≤ d) (h₂ : d + 8 ≤ k + 16) (h₃ : k + 16 ≤ 1280) :
      (sub s₀ k 16).Contains (off (cx s₀) d) (64 / 8) :=
    contains_sub s₀ h₁ h₂ h₃
  exact ((((Frame.refl _ m).writeW (by simp) _ (c 32 32 (by decide) (by decide) (by decide))).writeW
    (by simp) _ (c 32 40 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 288 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 296 (by decide) (by decide) (by decide))

theorem storeHm_frame (m : Mem) (p : Addr) (w0 w1 w2 : BitVec 64) :
    Frame [⟨p, 24⟩] m (Poly1305.AArch64.storeHm m p w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (Poly1305.AArch64.hR p).Contains (Poly1305.AArch64.off p d) (64 / 8) :=
    fun d hd => Poly1305.AArch64.hR_contains p hd
  exact (((Frame.refl _ m).writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

/-- The pointer and length of the data not yet absorbed. -/
theorem restP_eq (enc : Bool) (d : Addr) {o L T : Nat} (hT : 1 ≤ T) (hle : o + 512 * T ≤ L) :
    restP enc (d + BitVec.ofNat 64 (o + 512 * T)) (BitVec.ofNat 64 (L - (o + 512 * T))) =
      (d + BitVec.ofNat 64 (pre o enc T), BitVec.ofNat 64 (L - pre o enc T)) := by
  cases enc
  · rfl
  · simp only [restP, pre, ite_true]
    have e : o + 512 * T = o + 512 * (T - 1) + 512 := by omega
    refine Prod.ext ?_ ?_
    · show d + BitVec.ofNat 64 (o + 512 * T) - BitVec.ofNat 64 512 = _
      rw [e, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
    · show BitVec.ofNat 64 (L - (o + 512 * T)) + BitVec.ofNat 64 512 = _
      rw [← BitVec.ofNat_add]; congr 1; omega

/-- The accumulator `polyIn` loads. -/
theorem acc_in {s₀ s₂ s₃ : State} {key msg : List Byte}
    (hr : Repr s₂.mem (off (cx s₀) 448) key msg) (x0₃ : s₃.gpr .x0 = off (cx s₀) 64)
    (a21 : s₃.gpr .x21 = s₂.mem.readW (off (cx s₀) 448) 64)
    (a22 : s₃.gpr .x22 = s₂.mem.readW (off (cx s₀) 456) 64)
    (a23 : s₃.gpr .x23 = s₂.mem.readW (off (cx s₀) 464) 64)
    {a b : BitVec 64} (m₃ : s₃.mem = memIn s₂.mem (cx s₀) a b) :
    Acc (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16)))
      (VG.Spec.Poly1305.accumulate (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg)
      s₃ := by
  have hA := hr.2.2
  rw [leNum_words] at hA
  have hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  have r0 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off =
      s₂.mem.readW (off (cx s₀) 472) 64 &&& M0 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 224 = off (cx s₀) 288 from off_off _ 64 224, memIn_288]
  have r1 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off =
      s₂.mem.readW (off (cx s₀) 480) 64 &&& M1 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 232 = off (cx s₀) 296 from off_off _ 64 232, memIn_296]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Poly.hval, a21, a22, a23]; rw [hA]
  · rw [a23]; rw [← hA] at hlt; exact h2_le hlt
  · simp only [Poly.rval, r0, r1]
    rw [← clamp_words, ← Poly1305.AArch64.clamp_key, Poly1305.AArch64.off_24]
    exact congrArg (fun k => VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (List.take 16 k))) hr.2.1
  · rw [r0]; exact Poly1305.AArch64.Radix64.key0_lt _
  · rw [r1]; exact Poly1305.AArch64.Radix64.key1_lt _

/-! ## The chunks -/

theorem data_ctx {s₀ : State} (hp : APre e s₀) {k n : Nat} (h : k + n ≤ 1280) :
    (dR s₀).Disjoint (sub s₀ k n) :=
  hp.c_d.symm.sub_right (sub_ctx s₀ h)

/-- A prefix of the data outside a frame of the context. -/
theorem prefix_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {n : Nat} (hn : n ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n :=
  bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hn))
    (Nat.le_trans hn (Nat.le_of_lt (s₀.gpr .x5).isLt))

/-- The saved `x27` and `x28` are outside the stream's regions. -/
theorem saved_bulk {s₀ : State} (hp : APre e s₀) {o : Nat} (ho : o ≤ L s₀) {m m' : Mem}
    (hf : Frame (streamR s₀ o) m m') {d : Nat}
    (hd : d = 32 ∨ d = 40) : m'.readW (off (cx s₀) d) 64 = m.readW (off (cx s₀) d) 64 := by
  refine hf.readW (r := sub s₀ d 8) (Region.contains_self _ _) ?_ (by decide)
  have h₁ : d + 8 ≤ 1280 := by omega
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by omega) h₁ (by lit_omega)
  · exact (data_ctx hp h₁).symm.sub_right (dRo_sub s₀ ho)
  · exact sub_disj s₀ (by omega) h₁ (by lit_omega)

/-- The data's first `o` bytes are outside the stream's regions. -/
theorem prefix_streamR {s₀ : State} (hp : APre e s₀) {o : Nat} (ho : o ≤ L s₀) :
    ∀ r ∈ streamR s₀ o, (⟨dp s₀, o⟩ : Region).Disjoint r := by
  have hP : Region.Sub ⟨dp s₀, o⟩ (dR s₀) := Region.sub_prefix ho
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (data_ctx hp (by lit_omega)).sub_left hP
  · have := hp.wrap_d
    exact Offset.base_disjoint (dp s₀) (Nat.le_refl o) (by simp only [dp, L] at this ho ⊢; omega)
  · exact (data_ctx hp (by lit_omega)).sub_left hP

/-- The regions of the context `cryptStitched` writes, and the data. -/
theorem crypt_sub {s₀ : State} (r : Region) (k n : Nat) (h₁ : 64 ≤ k)
    (h₂ : k + n ≤ 472) (hr : r = sub s₀ k n) :
    ∃ r' ∈ [sub s₀ 64 408, sub s₀ 32 16, dR s₀], Region.Sub r r' :=
  ⟨sub s₀ 64 408, List.mem_cons_self, hr ▸ sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩

/-- At least 512 bytes from byte `o`: the chunks. -/
theorem long_crypted (enc : Bool) {s₀ : State} (hp : APre e s₀) {o : Nat} {s w : State}
    {key msg : List Byte} (E : Entry enc o s₀ s key msg w) {s₂ : State}
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = w.gpr .x22) (x2₂ : s₂.gpr .x2 = w.gpr .x23)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [] w s₂) (m₂ : s₂.mem = w.mem)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64)
    (hL : 512 ≤ L s₀ - o) :
    WP isa (.seq (.block polyIn) (.seq (Stitch.bulk sve enc) (.block (polyOut enc)))) s₂
      fun u => ∃ T, 1 ≤ T ∧ Crypted enc o s₀ s w key msg T u := by
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hL5
  have ho := E.le
  have o16 : o % 16 = 0 := by have := E.o64; omega_arith
  have i₂ := E.inv.kept k₂
  let msg' := msg ++ bytesAt (if enc then w.mem else s.mem) (dp s₀) o
  have hr₂ : Repr s₂.mem (off (cx s₀) 448) key msg' := by rw [m₂]; exact E.mac
  refine WP.seq ((polyIn_ok hp i₂.x21 i₂.rd i₂.wr).mono
    fun s₃ ⟨⟨a21, a22, a23, m₃, g₃, rd₃, wr₃⟩, v₃, sp₃, _, _⟩ => ?_)
  have x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by rw [g₃ _ (by decide), x0₂]
  have x1₃ : s₃.gpr .x1 = dp s₀ + BitVec.ofNat 64 o := by rw [g₃ _ (by decide), x1₂, E.x22]
  have x2₃ : s₃.gpr .x2 = BitVec.ofNat 64 (L s₀ - o) := by rw [g₃ _ (by decide), x2₂, E.x23]
  have x3₃ : s₃.gpr .x3 = off (cx s₀) 128 := by rw [g₃ _ (by decide), x3₂]
  have ha := acc_in hr₂ x0₃ a21 a22 a23 m₃
  refine WP.seq ((WP.otherV (bulkA_ok enc hp ho x0₃ x1₃ x2₃ x3₃ hL (by rw [wr₃, i₂.wr]) ha)
    (bulk_otherV sve enc)).mono fun s₄ ⟨⟨⟨T, hB⟩, rd₄, wr₄, sp₄, f₄⟩, ov₄⟩ => ?_)
  have hi := hB.inv
  have x0₄ : s₄.gpr .x0 = off (cx s₀) 64 := by
    have e := hi.x0; simp only [State.withRegions_gpr, Stitch.st_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.st, x0₃] at e; exact e
  have x1₄ : s₄.gpr .x1 = dp s₀ + BitVec.ofNat 64 (o + 512 * T) := by
    have e := hi.x1; simp only [State.withRegions_gpr, Stitch.dp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.dp, x1₃] at e
    rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hLB : VG.Proof.ChaCha20.AArch64.Xor.L (s₃.withRegions [] (streamR s₀ o)) = L s₀ - o := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, x2₃, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - (o + 512 * T)) := by
    have e := hi.x2; simp only [State.withRegions_gpr, Stitch.L_rebase, hLB] at e
    rw [e, Nat.sub_sub]
  have x3₄ : s₄.gpr .x3 = off (cx s₀) 128 := by
    have e := hi.x3; simp only [State.withRegions_gpr, Stitch.bp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.bp, x3₃] at e; exact e
  have le₄ : o + 512 * T ≤ L s₀ := by
    have e := hi.le; simp only [Stitch.L_rebase, hLB] at e; omega_arith
  refine (polyOut_ok hp enc x0₄ (by rw [rd₄, rd₃, i₂.rd]) (by rw [wr₄, wr₃, i₂.wr])).mono
    fun s₅ ⟨⟨hv₅, m₅, x21₅, x27₅, x28₅, x22₅, x23₅, g₅, rd₅, wr₅⟩, vv₅, sp₅, _, _⟩ => ⟨T, hB.pos, ?_⟩
  -- Memory.
  have f₂₃ : Frame (inR s₀) s₂.mem s₃.mem := by rw [m₃]; exact memIn_frame _ _ _
  have f₄₅ : Frame [sub s₀ 448 24] s₄.mem s₅.mem := by rw [m₅]; exact storeHm_frame _ _ _ _ _
  have hF₂ : Frame [sub s₀ 64 408, sub s₀ 32 16, dR s₀] w.mem s₅.mem := by
    rw [← m₂]
    refine (f₂₃.sub ?_).trans ((f₄.sub ?_).trans (f₄₅.sub ?_)) <;>
      intro r hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with hr | hr
      · exact crypt_sub r 288 16 (by decide) (by decide) hr
      · exact ⟨sub s₀ 32 16, by simp, hr ▸ fun _ h => h⟩
    · rcases hr with hr | hr | hr
      · exact crypt_sub r 64 64 (by decide) (by decide) hr
      · exact ⟨dR s₀, by simp, hr ▸ dRo_sub s₀ ho⟩
      · exact crypt_sub r 128 320 (by decide) (by decide) hr
    · exact crypt_sub r 448 24 (by decide) (by decide) hr
  have hd₂₃ : ∀ r ∈ inR s₀, (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)
  have hd₄₅ : ∀ r ∈ [sub s₀ 448 24], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)
  have d₀₃ (k : Nat) (hk : k < L s₀) :
      s₃.mem (dp s₀ + BitVec.ofNat 64 k) = w.mem (dp s₀ + BitVec.ofNat 64 k) := by
    rw [data_frame f₂₃ hd₂₃ hk, m₂]
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) =
      ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64) := by
    rw [stateAt_frame f₂₃ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      m₂, E.st]
  -- The data and the counter.
  have data₅ : ∀ k < L s₀, s₅.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < o + 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [data_frame f₄₅ hd₄₅ hk]
    by_cases hko : k < o
    · rw [f₄.bytes (prefix_streamR hp ho) (Nat.le_trans ho hL') hko, d₀₃ k hk, E.data k hk, ite_eq_left hko,
        ite_eq_left (by omega_arith)]
    · have hj : k - o < L s₀ - o := by omega_arith
      have e := hi.data (k - o) (by rw [Stitch.L_rebase, hLB]; exact hj)
      simp only [Stitch.dp_rebase, Stitch.D0_rebase, Stitch.KS_rebase] at e
      simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.D0, VG.Proof.ChaCha20.AArch64.Xor.KS,
        VG.Proof.ChaCha20.AArch64.Xor.S0, VG.Proof.ChaCha20.AArch64.Xor.dp,
        VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0₃, x1₃, hLB, st₃] at e
      have ek : dp s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 (k - o) = dp s₀ + BitVec.ofNat 64 k := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega_arith)]
      have o64 : 64 * (o / 64) = o := by have := E.o64; omega_arith
      have ks := ks1_off s₀ (q := o / 64) (k := k - o) (by omega_arith)
      rw [o64, Nat.add_sub_cancel' (by omega_arith)] at ks
      rw [ek, d₀₃ k hk, E.data k hk, ite_eq_right hko, ks] at e
      rw [e]
      by_cases hkT : k - o < 512 * T
      · rw [ite_eq_left hkT, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hkT, ite_eq_right (by omega_arith)]
  have cnt₅ : stateAt s₅.mem (off (cx s₀) 64) =
      ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (o / 64 + 8 * T) := by
    have e := hi.cnt
    simp only [Stitch.st_rebase, Stitch.S0_rebase] at e
    simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.S0,
      VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0₃, st₃] at e
    rw [stateAt_frame f₄₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), e, VG.Proof.ChaCha20.ctr_ctr]
  have r₄ (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₄.mem.readW (off (cx s₀) d) 64 = s₃.mem.readW (off (cx s₀) d) 64 := saved_bulk hp ho f₄ hd
  have un₅ : ∀ r ∈ untouched, s₅.gpr r = s₀.gpr r := by
    intro r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    have via (r : Reg) (hc : r ∈ preserved) (hn : r ∉ Stitch.accRegs)
        (h5 : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28])
        (h3 : r ∉ [Reg.x21, .x22, .x23, .x24, .x25]) (hu : r ∈ untouched) :
        s₅.gpr r = s₀.gpr r := by
      have e := hB.cs r hc
      simp only [State.withRegions_gpr] at e
      rw [g₅ r h5, e, rebase_of hn, State.withRegions_gpr, g₃ r h3,
        k₂.cs r hc (untouched_preserved r hu).2, E.inv.un r hu]
    have x2728 (r : Reg) (d : Nat) (hd : d = 32 ∨ d = 40) (hu : r ∈ untouched)
        (hx : s₅.gpr r = s₄.mem.readW (off (cx s₀) d) 64)
        (hm : (memIn s₂.mem (cx s₀) (s₂.gpr .x27) (s₂.gpr .x28)).readW (off (cx s₀) d) 64 = s₂.gpr r) :
        s₅.gpr r = s₀.gpr r := by
      rw [hx, r₄ d hd, m₃, hm, k₂.cs r (untouched_preserved r hu).1 (untouched_preserved r hu).2,
        E.inv.un r hu]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact x2728 _ 32 (.inl rfl) (by decide) x27₅ (memIn_800 _ _ _ _)
    · exact x2728 _ 40 (.inr rfl) (by decide) x28₅ (memIn_808 _ _ _ _)
  have hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg'
  have ac₄ := hB.acc
  have hX := hv₅ ac₄.h2
  rw [show hacc s₄ = Poly.hval (s₄.withRegions [] (streamR s₀ o)) from rfl, ac₄.h,
    Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)] at hX
  have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
  have hr1 := hr₂.2.1
  rw [k24] at hr1
  have hm16 : msg.length % 16 = 0 := by
    have := hr₂.1; simp only [msg', List.length_append, Poly1305.length_bytesAt] at this; omega_arith
  -- The bytes absorbed, in the order Poly1305 takes them.
  have habs : (msg ++ bytesAt (if enc then s₅.mem else s.mem) (dp s₀) (pre o enc T)) =
      msg' ++ (if enc then bytesAt s₄.mem (dp s₀ + BitVec.ofNat 64 o) (512 * (T - 1))
        else bytesAt s₃.mem (dp s₀ + BitVec.ofNat 64 o) (512 * T)) := by
    simp only [msg', List.append_assoc]
    refine congrArg (msg ++ ·) ?_
    cases enc
    · simp only [Bool.false_eq_true, ite_false, pre]
      rw [Poly1305.bytesAt_add]
      refine congrArg (_ ++ ·) ?_
      simp only [bytesAt]
      apply List.map_congr_left
      intro i hi
      have hi := List.mem_range.mp hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, d₀₃ (o + i) (by omega_arith), E.data (o + i) (by omega_arith),
        ite_eq_right (by omega_arith)]
    · simp only [ite_true, pre]
      have hP : Region.Sub ⟨dp s₀, o⟩ (dR s₀) := Region.sub_prefix ho
      have e1 : bytesAt s₅.mem (dp s₀) o = bytesAt w.mem (dp s₀) o := by
        rw [bytesAt_frame f₄₅ (p := dp s₀) (n := o) (fun r hr => (hd₄₅ r hr).sub_left hP) (by omega_arith),
          bytesAt_frame f₄ (p := dp s₀) (n := o) (prefix_streamR hp ho) (by omega_arith),
          bytesAt_frame f₂₃ (p := dp s₀) (n := o) (fun r hr => (hd₂₃ r hr).sub_left hP) (by omega_arith), m₂]
      have e2 : bytesAt s₅.mem (dp s₀ + BitVec.ofNat 64 o) (512 * (T - 1)) =
          bytesAt s₄.mem (dp s₀ + BitVec.ofNat 64 o) (512 * (T - 1)) :=
        bytesAt_frame f₄₅ (fun r hr => (hd₄₅ r hr).sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith)
      rw [Poly1305.bytesAt_add, e1, e2]
  refine ⟨⟨x21₅, un₅, by rw [sp₅, sp₄, sp₃, k₂.sp, E.inv.sp], by rw [rd₅, rd₄, rd₃, i₂.rd],
      by rw [wr₅, wr₄, wr₃, i₂.wr], E.inv.saved.frame hF₂ ?_, E.inv.frame.trans (hF₂.sub ?_)⟩,
    le₄, by have e := hB.rest; rw [hLB] at e; omega_arith, by rw [g₅ _ (by decide), x0₄],
    by rw [g₅ _ (by decide), x1₄], by rw [g₅ _ (by decide), x2₄],
    by rw [g₅ _ (by decide), x3₄], by rw [x22₅, x1₄, x2₄, restP_eq enc _ hB.pos le₄],
    by rw [x23₅, x1₄, x2₄, restP_eq enc _ hB.pos le₄], cnt₅, data₅, hF₂, ⟨?_, ?_, ?_⟩, fun r hr => ?_⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
  · rw [List.length_append, Poly1305.length_bytesAt]
    have := pre_mod o16 enc T; omega_arith
  · rw [k24, bytesAt_frame hF₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact (data_ctx hp (by lit_omega)).symm) (by lit_omega), ← m₂]
    exact hr1
  · rw [m₅, Poly1305.AArch64.storeHm_acc, ← m₅]
    show Poly1305.AArch64.Radix64.hval s₅ = _
    rw [hX, habs, Poly1305.accumulate_append hr₂.1]
    cases enc
    · simp only [Bool.false_eq_true, ite_false, State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.dp,
        State.withRegions_gpr, x1₃]
    · simp only [ite_true, State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.dp,
        State.withRegions_gpr, x1₃]
  · have e4 : s₄.v r = s₃.v r := by
      by_cases h8 : r = .v8
      · subst h8; simpa using hB.v8
      by_cases h9 : r = .v9
      · subst h9; simpa using hB.v9
      exact ov₄ r hr h8 h9
    rw [vv₅, e4, v₃, ← (E.vec r hr)]; exact v₂ r hr

/-- The whole chunks, from byte `o`. -/
theorem cryptStitched_ok (enc : Bool) (he : enc = false) {s₀ : State} (hp : APre e s₀) {o : Nat}
    {s w : State} {key msg : List Byte} (E : Entry enc o s₀ s key msg w) :
    WP isa (cryptStitched sve enc) w fun u => ∃ T, Crypted enc o s₀ s w key msg T u := by
  unfold cryptStitched
  rw [show afterBulk sve enc = .block (polyOut enc) by simp only [afterBulk, he, Bool.false_eq_true,
    ite_false]]
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hLo : L s₀ - o < 2 ^ 64 := by omega
  refine WP.seq ((setup_ok E.inv.x21).mono fun s₂ ⟨x0₂, x1₂, x2₂, x3₂, x5₂, k₂, m₂, v₂⟩ => ?_)
  rw [E.x23, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLo] at x5₂
  apply WP.ite (decide (L s₀ - o < 512)) (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short x5₂)
  · intro hs
    exact WP.block_nil ⟨0, short_crypted enc E x0₂ x1₂ x2₂ x3₂ k₂ m₂ v₂ (of_decide_eq_true hs)⟩
  · intro hs
    exact (long_crypted enc hp E x0₂ x1₂ x2₂ x3₂ k₂ m₂ v₂
      (by have := of_decide_eq_false hs; omega)).mono fun _ ⟨T, _, hc⟩ => ⟨T, hc⟩

/-! ## When encrypting -/

/-- What `cryptStitched` leaves when encrypting, from `s`: the data's first `P`
bytes encrypted from counter 1, the counter advanced past them if data
follows, the stream's arguments set to the rest, the first `A` bytes absorbed,
and the rest's pointer and length in `x22`, `x23`. -/
structure Sealed (s₀ s w : State) (key msg : List Byte) (P A : Nat) (u : State) : Prop where
  inv : Inv0 s₀ u
  le : P ≤ L s₀
  aP : A ≤ P
  a16 : A % 16 = 0
  p64 : P < L s₀ → P % 64 = 0
  x0 : u.gpr .x0 = off (cx s₀) 64
  x1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 P
  x2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - P)
  x3 : u.gpr .x3 = off (cx s₀) 128
  x22 : u.gpr .x22 = dp s₀ + BitVec.ofNat 64 A
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀ - A)
  cnt : P < L s₀ →
    stateAt u.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (P / 64)
  data : ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 408, sub s₀ 32 16, dR s₀] w.mem u.mem
  mac : Repr u.mem (off (cx s₀) 448) key (msg ++ bytesAt u.mem (dp s₀) A)
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem Crypted.sealed {s₀ s w : State} {key msg : List Byte} {o T : Nat} {u : State}
    (h : Crypted true o s₀ s w key msg T u) (ho : o % 64 = 0) :
    Sealed s₀ s w key msg (o + 512 * T) (pre o true T) u :=
  ⟨h.inv, h.le, pre_le o true T, pre_mod (by omega) true T, fun _ => by omega, h.x0, h.x1, h.x2, h.x3,
    h.x22, h.x23, fun _ => by rw [h.cnt, show (o + 512 * T) / 64 = o / 64 + 8 * T by omega], h.data,
    h.frame, by simpa only [ite_true] using h.mac, h.vec⟩

end VG.Proof.ChaCha20Poly1305.AArch64
