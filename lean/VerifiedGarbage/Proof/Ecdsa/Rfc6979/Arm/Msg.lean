import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy

/-!
# Deterministic ECDSA on 32-bit ARM: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): `V` copied from the frame (`r8`), the byte `b`, then the private
key (`r5`) and `h` copied (`head_ok`, `tail_ok`), each to `scratch` (`r11`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (wp_mov wp_strb op2_imm)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `V`, of `D` bytes, and `h`, in the frame. -/
abbrev vOf {dn : Nat} (L : Lay dn) (D : Nat) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 88) D
abbrev hOf {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 152) 32

/-- Where the messages are. -/
abbrev msgA {dn : Nat} (L : Lay dn) : Addr := State.addr L.scr + BitVec.ofNat 64 2256

theorem ptr_r0 : ∀ r ∈ ptrRegs, r ≠ .r0 := by decide

/-- `4 K` bytes copied to `scratch + d` by `copyN`, with `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} (hs : u.gpr src = S)
    (hsr : src ≠ .r0) {so d K : Nat} (hd : d + 4 * K ≤ 4096) (hso : so + 4 * K ≤ 4096)
    (hsn : S.toNat + so + 4 * K ≤ 2 ^ 32)
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + 4 * j)) 4)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, 4 * K⟩
      ⟨State.addr L.scr + BitVec.ofNat 64 d, 4 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .r11 d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨State.addr L.scr + BitVec.ofNat 64 d, 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 d) (4 * K) =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) (4 * K) := by
  have := hL.nc
  refine WP.mono (copyN_ok (K := K) (by decide) hsr hsep hsn (by omega) hso hd K (Nat.le_refl _) u hs hc.r11 hr
    fun j hj => hc.inScrW (by omega))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ => ?_
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)),
    hg, hf, hb⟩

theorem byte_self (m : Mem) (a : Addr) (v : BitVec 8) : m.writeW a v a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, Nat.reduceDiv,
    Nat.zero_lt_one, ite_true]
  exact BitVec.extractLsb'_eq_self

theorem setw8 (b : Nat) : (BitVec.ofNat 32 b).setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The byte `b` stored at `scratch + o`, through `r0`. -/
theorem strb_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {b o : Nat} (hb : b < 2) (ho : o < 4096) :
    WP isa (.block [.mov .r0 (.imm (BitVec.ofNat 32 b)), .strb .r0 .r11 o]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (State.addr L.scr + BitVec.ofNat 64 o) (BitVec.ofNat 8 b) :=
  wp_mov (op2_imm (by rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide)) fun s₁ u₁ =>
    wp_strb (a := State.addr L.scr + BitVec.ofNat 64 o) ho
      (by rw [u₁.other _ (by decide), hc.r11]; exact scrA hL (by omega))
      (by rw [u₁.wr]; exact hc.inScrW (by omega)) fun s₂ m₂ =>
      WP.block_nil ⟨by rw [m₂.rd, u₁.rd], by rw [m₂.wr, u₁.wr], by rw [m₂.sp, u₁.sp],
        fun r hr => by rw [m₂.gpr, u₁.other _ hr], by rw [m₂.mem, u₁.mem, u₁.gpr, setw8]⟩

theorem fp_toNat' (hL : L.Ok) : L.fp.toNat = L.sp.toNat - 200 := by
  have := hL.nB
  exact VG.Arm.FrameStack.sub_toNat' (by omega)

/-- `V ‖ b`, for `V` of `D` bytes. -/
theorem head_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2) {D : Nat} (hD : D ≤ 64)
    (hD4 : D % 4 = 0) :
    WP isa (.block (Cfg.copyN (D / 4) .r8 fV .r11 sMsg ++
      ([.mov .r0 (.imm (BitVec.ofNat 32 b)), .strb .r0 .r11 (sMsg + D)] : List Instr))) t fun u =>
      Ctx L g m₀ u ∧ (∀ r, r ≠ .r0 → u.gpr r = t.gpr r) ∧
      Frame [⟨msgA L, D + 1⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (msgA L) (D + 1) = vOf L D t.mem ++ [BitVec.ofNat 8 b] := by
  have e4 : 4 * (D / 4) = D := by omega
  have := L.sp.isLt; have := fp_toNat' hL
  simp only [fV, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (src := .r8) hc.r8 (by decide) (so := 64) (d := 2256) (K := D / 4) (by omega)
    (by omega) (by omega) (fun j hj => by rw [hL.fpA0, Offset.add_add]; exact hc.inFr (by omega) (by omega))
    (by rw [hL.fpA0, Offset.add_add]; exact hL.stk_scr (by omega) (by omega)))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [e4] at hf₂ hb₂
  refine WP.mono (strb_ok hL hc₂ hb (o := 2256 + D) (by omega)) fun u₃ ⟨hrd₃, hwr₃, hsp₃, hg₃, hm₃⟩ => ?_
  have hf₃ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 (2256 + D), 1⟩] u₂.mem u₃.mem := by
    rw [hm₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep hL hrd₃ hwr₃ hsp₃ (fun r hr => hg₃ r (ptr_r0 r hr)) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)),
    fun r hr => (hg₃ r hr).trans (hg₂ r hr), ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt u₃.mem (State.addr L.scr + BitVec.ofNat 64 2256) D =
        Spec.Sha256.bytesAt u₂.mem (State.addr L.scr + BitVec.ofNat 64 2256) D :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    rw [e₁, hb₂, hL.fpA0, Offset.add_add]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + 64)) D ++ y) ?_
    show [u₃.mem (State.addr L.scr + BitVec.ofNat 64 (2256 + D) + BitVec.ofNat 64 0)] = _
    rw [BitVec.add_zero, hm₃, byte_self]

/-- `‖ d ‖ h`, after `D + 1` bytes. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {D : Nat} (hD : D ≤ 64) :
    WP isa (.block (Cfg.copyN 8 .r5 0 .r11 (sMsg + D + 1) ++ Cfg.copyN 8 .r8 fH .r11 (sMsg + D + 33))) u
      fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
        Frame [⟨State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1), 64⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1)) 64 =
          Spec.Sha256.bytesAt u.mem (State.addr L.d) 32 ++ hOf L u.mem := by
  have := L.sp.isLt; have := fp_toNat' hL; have := hL.nd
  simp only [fH, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (src := .r5) hc.r5 (by decide) (so := 0) (d := 2256 + D + 1) (K := 8) (by omega)
    (by omega) (by omega) (fun j hj => hc.inD (by omega))
    (hL.dc.sub_left (Offset.sub_base _ (by omega)) |>.sub_right (Offset.sub_base _ (by omega))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  refine WP.mono (copy_ok hL hc₂ (src := .r8) hc₂.r8 (by decide) (so := 128) (d := 2256 + D + 33) (K := 8)
    (by omega) (by omega) (by omega)
    (fun j hj => by rw [hL.fpA0, Offset.add_add]; exact hc₂.inFr (by omega) (by omega))
    (by rw [hL.fpA0, Offset.add_add]; exact hL.stk_scr (by omega) (by omega)))
    fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, fun r hr => (hg₃ r hr).trans (hg₂ r hr), ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [Proof.Hmac.Common.bytesAt_add _ _ 32 32, Offset.add_add, show 2256 + D + 1 + 32 = 2256 + D + 33 by omega,
      show (32 : Nat) = 4 * 8 from rfl, hb₃,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂, BitVec.add_zero]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem (State.addr L.d) (4 * 8) ++ y) ?_
    rw [hL.fpA0, Offset.add_add]
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`) at `scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2) (full : Bool) {D : Nat}
    (hD : D ≤ 64) (hD4 : D % 4 = 0) :
    WP isa (.block (Cfg.msg D b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨msgA L, D + 65⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (msgA L) (if full then D + 65 else D + 1) =
        vOf L D t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) 32 ++ hOf L t.mem else []) := by
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hb hD hD4) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)
  · simp only [Cfg.msg, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hb hD hD4) fun u ⟨hcu, hg, hf, hb⟩ =>
      WP.mono (tail_ok hL hcu hD) fun u' ⟨hcu', _, hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
    · rw [show D + 65 = (D + 1) + 64 by omega, Proof.Hmac.Common.bytesAt_add _ _ (D + 1) 64, Offset.add_add,
        show 2256 + (D + 1) = 2256 + D + 1 by omega, hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb]
      refine congrArg (fun y => vOf L D t.mem ++ [BitVec.ofNat 8 b] ++ y) ?_
      simp only [hOf]
      rw [bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.dc.sub_right (Offset.sub_base _ (by omega))) (by omega),
        bytesAt_frame hf (p := L.B + BitVec.ofNat 64 152) (n := 32) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by omega) (by omega)) (by omega)]

end VG.Proof.Ecdsa.Rfc6979.Arm
