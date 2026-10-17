module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on 32-bit ARM: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): all 64 bytes of `V`'s place copied from the frame (`r8`) to
`scratch` (`r11`), then, from `scratch + D` (`r1`, from the hash function's
code), the byte `b`, the private key (`r5`) and `h`, from the frame
(`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (wp_mov wp_strb wp_str wp_dp op2_imm op2_reg dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `V`, of `D` bytes, in the frame. -/
abbrev vOf {dn : Nat} (L : Lay dn) (D : Nat) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 88) D

/-- `h`, of `Q` bytes, in the frame. -/
abbrev hOf {dn : Nat} (L : Lay dn) (Q : Nat) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 152) Q

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
  refine WP.mono (copyN_ok (K := K) (by decide) hsr hsep hsn (by omega_arith) hso hd K (Nat.le_refl _) u hs hc.r11 hr
    fun j hj => hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ => ?_
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)),
    hg, hf, hb⟩

theorem byte_self (m : Mem) (a : Addr) (v : BitVec 8) : m.writeW a v a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, Nat.reduceDiv,
    Nat.zero_lt_one, ite_true]
  exact BitVec.extractLsb'_eq_self

theorem setw8 (b : Nat) : (BitVec.ofNat 32 b).setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- `Q` bytes copied to `scratch + o + d` by `copyBytes`, through `r1 = scratch + o`, with `Ctx` kept. -/
theorem copyR_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} (hs : u.gpr src = S)
    (hsr : src ≠ .r0) {o : Nat} (h1 : u.gpr .r1 = L.scr + BitVec.ofNat 32 o) (ho : o ≤ 64) {so d Q : Nat}
    (h4 : 4 ≤ Q) (hd : d + Q ≤ 4096) (hso : so + Q ≤ 4096) (hsn : S.toNat + so + Q ≤ 2 ^ 32)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + j)) 4)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, Q⟩ ⟨State.addr L.scr + BitVec.ofNat 64 (o + d), Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .r1 d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨State.addr L.scr + BitVec.ofNat 64 (o + d), Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 (o + d)) Q =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) Q := by
  have := hL.nc
  have eA : State.addr (L.scr + BitVec.ofNat 32 o) + BitVec.ofNat 64 d = State.addr L.scr + BitVec.ofNat 64 (o + d) := by
    rw [scrA hL (by omega_arith), Offset.add_add]
  have hn : (L.scr + BitVec.ofNat 32 o).toNat = L.scr.toNat + o := scr_toNat hL (by omega_arith)
  refine WP.mono (copyBytes_ok (by decide) hsr (by rw [eA]; exact hsep) hsn (by rw [hn]; omega_arith) hso hd h4 hs h1 hr
    fun j hj => by rw [scrA hL (by omega_arith), Offset.add_add]; exact hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ => ?_
  rw [eA] at hf hb
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)),
    hg, hf, hb⟩

/-- The frame does not wrap. -/
theorem fp_fit (hL : L.Ok) : L.fp.toNat + 432 ≤ 2 ^ 32 := by
  have := hL.nB; have := hL.nA
  have : L.fp.toNat = L.sp.toNat - 432 := VG.Arm.FrameStack.sub_toNat' (by omega)
  omega

theorem fpB (hL : L.Ok) (o : Nat) : State.addr L.fp + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (24 + o) := by
  rw [hL.fpA0, Offset.add_add]

/-- The tail `‖ d ‖ h` of a full message, from `scratch + D + 2257`, through `r1 = scratch + D`. -/
theorem tail_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g m₀ u) {D : Nat} (hD : D ≤ 64)
    (h1 : u.gpr .r1 = L.scr + BitVec.ofNat 32 D) :
    WP isa (.block (Cfg.copyBytes P.Q .r5 0 .r1 (sMsg + 1) ++ Cfg.copyBytes P.Q .r8 fH .r1 (sMsg + 1 + P.Q))) u
      fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
        Frame [⟨State.addr L.scr + BitVec.ofNat 64 (D + 2257), 2 * P.Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 (D + 2257)) (2 * P.Q) =
          Spec.Sha256.bytesAt u.mem (State.addr L.d) P.Q ++ hOf L P.Q u.mem := by
  have := L.sp.isLt; have := hL.nd; have := hL.B_fit; have := hL.nc
  have hQ := P.wsizes
  have hqq : L.q = P.Q := hq.1
  simp only [sMsg, fH]
  rw [WP.block_append_iff]
  refine WP.mono (copyR_ok hL hc (src := .r5) hc.r5 (by decide) h1 hD (so := 0) (d := 2257) (by anums)
    (by anums) (by anums) (by anums) (fun j hj => hc.inD (by rw [hqq]; anums) (by anums))
    ((hL.dc.sub_left (Offset.sub_base _ (by rw [hqq]; anums))).sub_right (Offset.sub_base _ (by anums))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have h1' : u₂.gpr .r1 = L.scr + BitVec.ofNat 32 D := by rw [hg₂ _ (by decide), h1]
  have hr8 : State.addr (u₂.gpr .r8) = State.addr L.fp := by rw [hc₂.r8]
  refine WP.mono (copyR_ok hL hc₂ (src := .r8) rfl (by decide) h1' hD (so := 128) (d := 2257 + P.Q) (by anums)
    (by anums) (by anums) (by rw [hc₂.r8]; have := fp_fit hL; anums)
    (fun j hj => by rw [hr8, fpB hL]; exact hc₂.inFr (by omega_arith) (by anums))
    (by rw [hr8, fpB hL]; exact hL.stk_scr (by anums) (by anums)))
    fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, fun r hr => (hg₃ r hr).trans (hg₂ r hr), ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
  · rw [show 2 * P.Q = P.Q + P.Q by omega_arith, Proof.Hmac.Common.bytesAt_add _ _ P.Q P.Q, Offset.add_add,
      show D + 2257 + P.Q = D + (2257 + P.Q) by omega_arith, hb₃,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith),
      hb₂, BitVec.add_zero, hr8, fpB hL]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem (State.addr L.d) P.Q ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by omega_arith)

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2) (full : Bool) :
    WP isa (.block (Cfg.msg P.Q b full)) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨msgA L, 200⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (msgA L) (if full then P.F.H.D + 2 * P.Q + 1 else P.F.H.D + 1) =
        vOf L P.F.H.D t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf L P.Q t.mem else []) := by
  have nc := hL.nc
  have hb' := hL.B_fit
  have hQ := P.wsizes
  have hD := P.sizes
  simp only [Cfg.msg, List.append_assoc]
  rw [WP.block_append_iff]
  -- `V`'s 64 bytes.
  refine WP.mono (copy_ok hL hc (src := .r8) hc.r8 (by decide) (so := 64) (d := 2256) (K := 16) (by omega_arith)
    (by omega_arith) (by have := fp_fit hL; omega_arith)
    (fun j hj => by rw [fpB hL]; exact hc.inFr (by omega_arith) (by omega_arith))
    (by rw [fpB hL]; exact hL.stk_scr (by omega_arith) (by omega_arith)))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  -- `r1 = scratch + D`, and `b`.
  simp only [List.cons_append, List.nil_append]
  refine dOut_ok hq hc₁ (d := .r1) (by decide) fun u₂ hc₂ hm₂ hv₂ hk₂ => ?_
  refine wp_dp (op2_reg _ _) fun u₃ v₃ => ?_
  have hc₃ := hc₂.upd v₃ (by decide)
  have h1 : u₃.gpr .r1 = L.scr + BitVec.ofNat 32 P.F.H.D := by rw [v₃.gpr, dpVal, hc₂.r11, hv₂]
  have eb : State.addr (u₃.gpr .r1 + BitVec.ofNat 32 2256) = State.addr L.scr + BitVec.ofNat 64 (P.F.H.D + 2256) := by
    rw [h1, BitVec.add_assoc, BitVec.ofNat_add_ofNat, scrA hL (by anums)]
  refine wp_mov (op2_imm (by rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> decide)) fun u₄ v₄ => ?_
  refine wp_strb (a := State.addr L.scr + BitVec.ofNat 64 (P.F.H.D + 2256)) (by decide)
    (by rw [v₄.other _ (by decide)]; exact eb) (by rw [v₄.wr, v₃.wr]; exact hc₂.inScrW (by anums)) fun u₅ m₅ => ?_
  have hm₅ : u₅.mem = u₃.mem.writeW (State.addr L.scr + BitVec.ofNat 64 (P.F.H.D + 2256)) (BitVec.ofNat 8 b) := by
    rw [m₅.mem, v₄.mem, v₄.gpr, setw8]
  have hf₅ : Frame [⟨State.addr L.scr + BitVec.ofNat 64 (P.F.H.D + 2256), 1⟩] u₃.mem u₅.mem := by
    rw [hm₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₅ : Ctx L g m₀ u₅ := (hc₃.upd v₄ (by decide)).keep hL m₅.rd m₅.wr m₅.sp (fun r _ => by rw [m₅.gpr])
    (by rw [v₄.mem]; exact hf₅) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by anums))
  have hm₃ : u₃.mem = u₁.mem := by rw [v₃.mem, hm₂]
  have h9 : u₅.gpr .r9 = t.gpr .r9 := by
    rw [m₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), hk₂ _ (by decide), hg₁ _ (by decide)]
  -- The head `V ‖ b`, from `u₅`'s memory.
  have head : Spec.Sha256.bytesAt u₅.mem (msgA L) (P.F.H.D + 1) = vOf L P.F.H.D t.mem ++ [BitVec.ofNat 8 b] := by
    rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt u₅.mem (msgA L) P.F.H.D = Spec.Sha256.bytesAt u₁.mem (msgA L) P.F.H.D := by
      rw [← hm₃]
      exact bytesAt_frame hf₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    rw [e₁, bytesAt_take _ _ (show P.F.H.D ≤ 4 * 16 by anums), hb₁, ← bytesAt_take _ _ (show P.F.H.D ≤ 4 * 16 by anums),
      fpB hL, show 2256 + P.F.H.D = P.F.H.D + 2256 by omega_arith]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + 64)) P.F.H.D ++ y) ?_
    show [u₅.mem (State.addr L.scr + BitVec.ofNat 64 (P.F.H.D + 2256) + BitVec.ofNat 64 0)] = _
    rw [BitVec.add_zero, hm₅, byte_self]
  have hf₁₅ : Frame [⟨msgA L, 200⟩] t.mem u₅.mem := by
    refine (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hm₃ ▸ hf₅.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by anums)
  cases full
  · simp only [Bool.false_eq_true, ite_false]
    exact WP.block_nil ⟨hc₅, h9, hf₁₅, head⟩
  · simp only [ite_true]
    have h1₅ : u₅.gpr .r1 = L.scr + BitVec.ofNat 32 P.F.H.D := by rw [m₅.gpr, v₄.other _ (by decide), h1]
    refine WP.mono (tail_ok hL hq hc₅ (by anums) h1₅) fun u' ⟨hc', hg', hf', hb'⟩ => ⟨hc', ?_, ?_, ?_⟩
    · rw [hg' _ (by decide), h9]
    · refine hf₁₅.trans (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega_arith) (by anums)
    · rw [show P.F.H.D + 2 * P.Q + 1 = (P.F.H.D + 1) + 2 * P.Q by omega_arith,
        Proof.Hmac.Common.bytesAt_add _ _ (P.F.H.D + 1) (2 * P.Q), Offset.add_add,
        show 2256 + (P.F.H.D + 1) = P.F.H.D + 2257 by omega_arith, hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), head]
      have hdq : Spec.Sha256.bytesAt u₅.mem (State.addr L.d) P.Q = Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q :=
        bytesAt_frame hf₁₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix (by rw [hq.1]))).sub_right (Offset.sub_base _ (by omega_arith)))
          (by omega_arith)
      have hhq : hOf L P.Q u₅.mem = hOf L P.Q t.mem :=
        bytesAt_frame hf₁₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by anums) (by omega_arith)) (by omega_arith)
      rw [hdq, hhq, List.append_assoc]; rfl

end VG.Proof.Ecdsa.Rfc6979.Arm
