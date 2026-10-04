import VerifiedGarbage.Proof.AesCcm.Arm.Env
import VerifiedGarbage.Proof.AesGcm.Arm.Compare

/-!
# AES-CCM on ARMv7: checking a received tag (`recv`, `cmp o`)

Untrusted: everything here is checked by Lean. These are AES-GCM's pieces
(`Proof/AesGcm/Arm/Compare.lean`), with AES-CCM's environment: `recv` pads
the `r6` bytes of the received tag at `tag` with zeros at `W + 256`
(`recv_ok`); `cmp o` pads the first `r6` bytes of the tag at `W + o` at
`W + 240` and leaves 1 in `r0` if they are the received ones, 0 if not
(`cmp_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok covers_left bytesAt_frame length_bytesAt
  bytesAt_writeBytes_prefix writeBytes_frame' store4_zero_tail bytes_words words_eq_iff cmp_value runBlock_app_of
  Keeps add_ofNat_assoc add_ofNat_zero mem_store store4_eq gpr_store rd_store wr_store sp_store z_store c_store
  gpr_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags z_subFlags c_subFlags store32_eq store8_eq
  encodable_of_decide sepW)

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- A copy of `tl` bytes from `W + o` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {s : State} (he : Env k w sp R q1 s) {S : BitVec 32} {o d tl : Nat}
    (hod : o + 16 ≤ d ∨ d + 16 ≤ o) (ho : o + 16 ≤ 2560) (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (hSa : State.addr S = State.addr w + BitVec.ofNat 64 o) (hSn : S.toNat = w.toNat + o) {m₀ : Mem}
    (hm : s.mem = store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (hr1 : s.gpr .r1 = S)
    (hr2 : s.gpr .r2 = w + BitVec.ofNat 32 d) (hr3 : s.gpr .r3 = BitVec.ofNat 32 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 d) 16 =
        bytesAt m₀ (State.addr w + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ s'.mem ∧ LoopOut s S (w + BitVec.ofNat 32 d) tl s' := by
  have eD := L.wA (d := d) (by omega)
  have ww := L.ww
  have lp : LoopPre s S (w + BitVec.ofNat 32 d) tl := by
    refine ⟨hr1, hr2, hr3, h1, by omega, by omega, by rw [L.wN (by omega)]; omega, ?_, ?_, ?_⟩
    · rw [hSa]; exact covers_left (he.perm.wC (by omega))
    · rw [eD]; exact he.perm.wC (by omega)
    · rw [hSa, eD]; exact L.w_w (by omega) (by omega) (by omega)
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm', lo⟩ => ?_
  rw [hm, hSa, eD] at hm'
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) :=
    Cmac.frame_store4 _ _ _ _ _
  have hx : bytesAt (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (State.addr w + BitVec.ofNat 64 o) tl =
      bytesAt m₀ (State.addr w + BitVec.ofNat 64 o) tl :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by omega) (by omega)) (by omega)
  rw [hx] at hm'
  have hlen := length_bytesAt m₀ (State.addr w + BitVec.ofNat 64 o) tl
  refine ⟨?_, ?_, lo⟩
  · rw [hm', bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, store4_zero_tail _ _ h16]
  · rw [hm']
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- `zero16 d`: the 16 bytes at `W + d` zeroed. -/
theorem zero16_ok {s : State} (he : Env k w sp R q1 s) {d : Nat} (hd : d + 16 ≤ 2560) (ed₁ : d + 12 < 4096) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 d) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r0 = 0 := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show d + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show d + 4 + 4 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show d + 8 + 4 ≤ 2560 by omega)
  have w₃ := he.perm.wW (show d + 12 + 4 ≤ 2560 by omega)
  have e₀ := L.wA (d := d) (by omega)
  have e₁ := L.wA (d := d + 4) (by omega)
  have e₂ := L.wA (d := d + 8) (by omega)
  have e₃ := L.wA (d := d + 12) (by omega)
  have o₀ : d < 4096 := by omega
  have o₁ : d + 4 < 4096 := by omega
  have o₂ : d + 8 < 4096 := by omega
  refine ⟨_, by simp only [zero16]; arun [h11, e₀, e₁, e₂, e₃, w₀, w₁, w₂, w₃, o₀, o₁, o₂, ed₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · intro r a; simp [gpr_setReg, a]
  · rfl
  · rfl
  · rfl
  · simp [gpr_setReg]

/-- `cmpTail`: `r0` is 1 iff the 16 bytes at `W + 240` and `W + 256` are equal. -/
theorem cmpTail_ok {s : State} (he : Env k w sp R q1 s) :
    ∃ s', runBlock isa cmpTail s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 240) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 240 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 244 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 248 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 252 + 4 ≤ 2560 by decide)
  have q₀ := he.perm.wR (show 256 + 4 ≤ 2560 by decide)
  have q₁ := he.perm.wR (show 260 + 4 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 264 + 4 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 268 + 4 ≤ 2560 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (240 + 4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (256 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)] s₂ =
      some s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s₂.gpr r) ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - ((s₂.gpr .r0 ||| (BitVec.ofNat 32 0 - s₂.gpr .r0)) >>> 31) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · intro r x y; simp [gpr_setReg, x, y]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show cmpTail = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

/-- A copy of `tl` bytes from `S`, apart from `W + d`, to `W + d`, which
holds 16 zero bytes. -/
theorem padCopyAny_ok {s : State} (he : Env k w sp R q1 s) {S : BitVec 32} {d tl : Nat}
    (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hSr : Covers [⟨State.addr S, tl⟩] (s.rd ++ s.wr))
    (hSf : S.toNat + tl ≤ 2 ^ 32) (hSd : (⟨State.addr S, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 16⟩)
    {m₀ : Mem} (hm : s.mem = store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (hr1 : s.gpr .r1 = S)
    (hr2 : s.gpr .r2 = w + BitVec.ofNat 32 d) (hr3 : s.gpr .r3 = BitVec.ofNat 32 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 d) 16 =
        bytesAt m₀ (State.addr S) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ s'.mem ∧ LoopOut s S (w + BitVec.ofNat 32 d) tl s' := by
  have eD := L.wA (d := d) (by omega)
  have ww := L.ww
  have lp : LoopPre s S (w + BitVec.ofNat 32 d) tl := by
    refine ⟨hr1, hr2, hr3, h1, by omega, hSf, by rw [L.wN (by omega)]; omega, hSr, ?_, ?_⟩
    · rw [eD]; exact he.perm.wC (by omega)
    · rw [eD]; exact hSd.sub_right (Region.sub_prefix h16)
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm', lo⟩ => ?_
  rw [hm, eD] at hm'
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) :=
    Cmac.frame_store4 _ _ _ _ _
  have hx : bytesAt (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (State.addr S) tl =
      bytesAt m₀ (State.addr S) tl :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega)
  rw [hx] at hm'
  have hlen := length_bytesAt m₀ (State.addr S) tl
  refine ⟨?_, ?_, lo⟩
  · rw [hm', bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, store4_zero_tail _ _ h16]
  · rw [hm']
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- `recv` (AES-GCM's): the received tag, the `r6` bytes at `T` (the stack
argument at `sp + 16`), padded with zeros at `W + 256`. -/
theorem recv_ok {s : State} (he : Env k w sp R q1 s) {T : BitVec 32} {tl : Nat}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hTr : Covers [⟨State.addr T, tl⟩] (s.rd ++ s.wr)) (hTf : T.toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa recv s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr T) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₀, run₀, h1₀, g₀, k₀⟩ : ∃ s₀, runBlock isa [.ldrSp .r1 16] s = some s₀ ∧ s₀.gpr .r1 = T ∧
      (∀ r, r ≠ .r1 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by arun [hTi, hTv], ?_, ?_, ?_⟩
    · simp [gpr_setReg, hTv]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₀ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₀ _ (by decide)) k₀.sp k₀.rd k₀.wr
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := zero16_ok L he₀ (d := rO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he₀.r11]
  obtain ⟨s₂, run₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r11 rO, .mov .r3 (.reg .r6)] s₁ = some s₂ ∧
      s₂.gpr .r2 = w + BitVec.ofNat 32 256 ∧ s₂.gpr .r3 = BitVec.ofNat 32 tl ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [rO]; arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), g₀ .r6 (by decide), h6]
    · intro r x y; simp [gpr_setReg, x, y]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have run : runBlock isa (.ldrSp .r1 16 :: zero16 rO ++ [addI .r2 .r11 rO, .mov .r3 (.reg .r6)]) s = some s₂ :=
    runBlock_app_of (a := [.ldrSp .r1 16]) run₀ (runBlock_app_of run₁ run₂)
  refine WP.seq (WP.of_runBlock ⟨s₂, run, ?_⟩)
  have he₂ := he₀.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have h1₂ : s₂.gpr .r1 = T := by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h1₀]
  have hTr₂ : Covers [⟨State.addr T, tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [k₂.rd, k₂.wr, rd₁, wr₁, k₀.rd, k₀.wr]; exact hTr
  refine WP.mono (padCopyAny_ok L he₂ (d := 256) (by decide) h1 h16 hTr₂ hTf hTd (m₀ := s.mem)
    (by rw [k₂.mem, hm₁, k₀.mem]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_
  refine ⟨hb, hf, fun r a b d e f => ?_, lo.rd.trans (k₂.rd.trans (rd₁.trans k₀.rd)),
    lo.wr.trans (k₂.wr.trans (wr₁.trans k₀.wr)), lo.sp.trans (k₂.sp.trans (sp₁.trans k₀.sp))⟩
  rw [lo.other r a b d e f, g₂ r d e, g₁ r a, g₀ r b]

/-- `cmp o`: the first `r6` bytes of the tag at `W + o`, padded with zeros at
`W + 240`, compared with the received tag at `W + 256`. -/
theorem cmp_ok {s : State} (he : Env k w sp R q1 s) {o : Nat} (ho : o = 0 ∨ o = 112) {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa (cmp o) s fun s' => s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := zero16_ok L he (d := vO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have eo : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 o, addI .r2 .r11 vO,
      .mov .r3 (.reg .r6)] s₁ = some s₂ ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 o ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 240 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [vO]; arun [eo], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), h6]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, runBlock_app_of run₁ run₂, ?_⟩)
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  refine WP.seq (WP.mono (padCopy_ok L he₂ (o := o) (d := 240) (by omega) (by omega) (by decide) h1 h16
    (L.wA (by omega)) (L.wN (by omega)) (m₀ := s.mem) (by rw [k₂.mem, hm₁]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := cmpTail_ok L he₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_, ?_, fun r a b d e f => ?_, k₄.rd.trans (lo.rd.trans (k₂.rd.trans rd₁)),
    k₄.wr.trans (lo.wr.trans (k₂.wr.trans wr₁)), k₄.sp.trans (lo.sp.trans (k₂.sp.trans sp₁))⟩
  · have h256 : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 :=
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [h0₄, hb, h256]
  · rw [k₄.mem]; exact hf
  · rw [g₄ r a b d, lo.other r a b d e f, g₂ r b d e, g₁ r a]

end

end VG.Proof.AesCcm.Arm
