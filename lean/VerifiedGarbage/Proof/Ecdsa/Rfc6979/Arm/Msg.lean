import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy

/-!
# Deterministic ECDSA on 32-bit ARM: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): `V` copied from the frame (`r8`), the byte `b`, then the private
key (`r5`) and `h` copied (`head_ok`, `tail_ok`), each to `scratch` (`r11`),
or, if `wide`, the private key, a zero word and the digest (`r6`), which
leaves `h` as `Q - D` zero bytes then the digest (`tailW_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (wp_mov wp_strb wp_str op2_imm)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `V`, of `D` bytes, in the frame. -/
abbrev vOf {dn : Nat} (L : Lay dn) (D : Nat) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 88) D

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

theorem fp_toNat' (hL : L.Ok) : L.fp.toNat = L.sp.toNat - (216 + 4 * L.e) := by
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

/-- `‖ d ‖ h`, `k` words each, after `D + 1` bytes. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {D k : Nat} (hD : D ≤ 64) (hq : 4 * k ≤ L.q)
    (hk : k ≤ 12) :
    WP isa (.block (Cfg.copyN k .r5 0 .r11 (sMsg + D + 1) ++ Cfg.copyN k .r8 fH .r11 (sMsg + D + 1 + 4 * k))) u
      fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
        Frame [⟨State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1), 8 * k⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1)) (8 * k) =
          Spec.Sha256.bytesAt u.mem (State.addr L.d) (4 * k) ++
            Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 152) (4 * k) := by
  have := L.sp.isLt; have := fp_toNat' hL; have := hL.nd
  simp only [fH, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (src := .r5) hc.r5 (by decide) (so := 0) (d := 2256 + D + 1) (K := k) (by omega)
    (by omega) (by omega) (fun j hj => hc.inD (by omega) (by omega))
    (hL.dc.sub_left (Offset.sub_base _ (by omega)) |>.sub_right (Offset.sub_base _ (by omega))))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  refine WP.mono (copy_ok hL hc₂ (src := .r8) hc₂.r8 (by decide) (so := 128) (d := 2256 + D + 1 + 4 * k) (K := k)
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
  · rw [show 8 * k = 4 * k + 4 * k by omega, Proof.Hmac.Common.bytesAt_add _ _ (4 * k) (4 * k), Offset.add_add,
      hb₃,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂, BitVec.add_zero]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem (State.addr L.d) (4 * k) ++ y) ?_
    rw [hL.fpA0, Offset.add_add]
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)

/-- `Q` bytes copied to `scratch + d` by `copyBytes`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} (hs : u.gpr src = S)
    (hsr : src ≠ .r0) {so d Q : Nat} (h4 : 4 ≤ Q) (hd : d + Q ≤ 4096) (hso : so + Q ≤ 4096)
    (hsn : S.toNat + so + Q ≤ 2 ^ 32)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + j)) 4)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, Q⟩ ⟨State.addr L.scr + BitVec.ofNat 64 d, Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .r11 d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨State.addr L.scr + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 d) Q =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) Q := by
  have := hL.nc
  refine WP.mono (copyBytes_ok (by decide) hsr hsep hsn (by omega) hso hd h4 hs hc.r11 hr
    fun j hj => hc.inScrW (by omega))
    fun u' ⟨hrd, hwr, hsp, hg, hf, hb⟩ => ?_
  exact ⟨hc.keep hL hrd hwr hsp (fun r hr => hg r (ptr_r0 r hr)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)),
    hg, hf, hb⟩

/-- The bytes of a zero word. -/
theorem bytesAt_writeW_zero (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 4) :
    Spec.Sha256.bytesAt (m.writeW p (0 : BitVec 32)) p k = List.replicate k 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [Spec.Sha256.bytesAt], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i - p).toNat = i := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [Mem.writeW, Mem.write, e, show i < 32 / 8 by omega, ite_true]
  apply BitVec.eq_of_toNat_eq; simp

/-- A zero word at `scratch + o`, through `r0`. -/
theorem zeroW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {o : Nat} (ho : o + 4 ≤ 4096) :
    WP isa (.block [.mov .r0 (.imm 0), .str .r0 .r11 o]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧ Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, 4⟩] u.mem u'.mem ∧
      ∀ k ≤ 4, Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 o) k = List.replicate k 0 := by
  refine wp_mov (op2_imm (v := 0) (by decide)) fun s₁ u₁ =>
    wp_str (a := State.addr L.scr + BitVec.ofNat 64 o) (by omega)
      (by rw [u₁.other _ (by decide), hc.r11]; exact scrA hL (by omega))
      (by rw [u₁.wr]; exact hc.inScrW (by omega)) fun s₂ m₂ => WP.block_nil ?_
  have hm : s₂.mem = u.mem.writeW (State.addr L.scr + BitVec.ofNat 64 o) (0 : BitVec 32) := by
    rw [m₂.mem, u₁.mem, u₁.gpr]
  have hf : Frame [⟨State.addr L.scr + BitVec.ofNat 64 o, 4⟩] u.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨(hc.upd u₁ (by decide)).keep hL m₂.rd m₂.wr m₂.sp (fun r _ => by rw [m₂.gpr]) (by rw [u₁.mem]; exact hf)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)),
    fun r hr => by rw [m₂.gpr, u₁.other _ hr], hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero _ _ hk⟩

/-- `‖ d ‖ h` for two `V`s to a candidate, `Q` bytes each, after `D + 1`
bytes: `h` is `Q - D` zero bytes then the digest. -/
theorem tailW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {D Q : Nat} (hD : D ≤ 64) (hD4 : D % 4 = 0)
    (h4 : 4 ≤ Q) (hQD : D ≤ Q) (hQD4 : Q ≤ D + 4) (hq : Q ≤ L.q) (hdn : D ≤ dn) :
    WP isa (.block (Cfg.copyBytes Q .r5 0 .r11 (sMsg + D + 1) ++
      ([.mov .r0 (.imm 0), .str .r0 .r11 (sMsg + D + 1 + Q)] : List Instr) ++
      Cfg.copyN (D / 4) .r6 0 .r11 (sMsg + 1 + 2 * Q))) u
      fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
        Frame [⟨State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
          Spec.Sha256.bytesAt u.mem (State.addr L.d) Q ++
            (List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt u.mem (State.addr L.dg) D) := by
  have nc := hL.nc
  have nd := hL.nd
  have ng := hL.ng
  have e4 : 4 * (D / 4) = D := by omega
  simp only [sMsg]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .r5) hc.r5 (by decide) (so := 0) (d := 2256 + D + 1) h4
    (by omega) (by omega) (by omega) (fun j hj => hc.inD (by omega) (by omega))
    ((hL.dc.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  rw [BitVec.add_zero] at hb₁
  refine WP.mono (zeroW_ok hL hc₁ (o := 2256 + D + 1 + Q) (by omega)) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  refine WP.mono (copy_ok hL hc₂ (src := .r6) hc₂.r6 (by decide) (so := 0) (d := 2256 + 1 + 2 * Q) (K := D / 4)
    (by omega) (by omega) (by omega) (fun j hj => hc₂.inDg (by omega) (by omega))
    (by rw [e4]; exact (hL.gc.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))))
    fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
  rw [e4, BitVec.add_zero] at hb₃
  rw [e4] at hf₃
  refine ⟨hc₃, fun r hr => (hg₃ r hr).trans ((hg₂ r hr).trans (hg₁ r hr)), ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    all_goals simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
  · have hg₁' : Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) D = Spec.Sha256.bytesAt u.mem (State.addr L.dg) D :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega))) (by omega)
    have hg₂' : Spec.Sha256.bytesAt u₂.mem (State.addr L.dg) D = Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) D :=
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega))) (by omega)
    rw [show 2 * Q = Q + ((Q - D) + D) by omega, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add _ _ (Q - D) D, Offset.add_add, Offset.add_add,
      show 2256 + D + 1 + Q + (Q - D) = 2256 + 1 + 2 * Q by omega, hb₃, hg₂', hg₁']
    congr 1
    · rw [bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₁]
    · refine congrArg (· ++ Spec.Sha256.bytesAt u.mem (State.addr L.dg) D) ?_
      rw [bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      exact hb₂ _ (by omega)

/-- `h` in the message: from the frame (`Q` bytes), or, if `wide`, `Q - D`
zero bytes then the digest. -/
abbrev hPart (wide : Bool) (Q D : Nat) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  if wide then List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt m (State.addr L.dg) D
  else Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 152) Q

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2) (full wide : Bool)
    {D k Q : Nat} (hD : D ≤ 64) (hD4 : D % 4 = 0) (h4 : 4 ≤ Q) (hQ : Q ≤ 72) (hq : Q ≤ L.q)
    (hA : full = true → wide = false → Q = 4 * k ∧ k ≤ 12)
    (hW : full = true → wide = true → D ≤ Q ∧ Q ≤ D + 4 ∧ D ≤ dn) :
    WP isa (.block (Cfg.msg k Q D b full wide)) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame [⟨msgA L, D + 2 * Q + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (msgA L) (if full then D + 2 * Q + 1 else D + 1) =
        vOf L D t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) Q ++ hPart wide Q D L t.mem else []) := by
  have nc := hL.nc
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hb hD hD4) fun u ⟨hcu, hg, hf, hb⟩ =>
      ⟨hcu, hg _ (by decide), hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)
  · simp only [Cfg.msg, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hb hD hD4) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    -- The tail, and what it is made of, unchanged by the head.
    suffices h : WP isa (.block (if wide then
          Cfg.copyBytes Q .r5 0 .r11 (sMsg + D + 1) ++
            ([.mov .r0 (.imm 0), .str .r0 .r11 (sMsg + D + 1 + Q)] : List Instr) ++
            Cfg.copyN (D / 4) .r6 0 .r11 (sMsg + 1 + 2 * Q)
        else Cfg.copyN k .r5 0 .r11 (sMsg + D + 1) ++ Cfg.copyN k .r8 fH .r11 (sMsg + D + 1 + 4 * k))) u
        fun u' => Ctx L g m₀ u' ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
          Frame [⟨State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
          Spec.Sha256.bytesAt u'.mem (State.addr L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
            Spec.Sha256.bytesAt u.mem (State.addr L.d) Q ++ hPart wide Q D L u.mem by
      refine WP.mono h fun u' ⟨hcu', hg', hf', hb'⟩ =>
        ⟨hcu', (hg' _ (by decide)).trans (hg _ (by decide)), ?_, ?_⟩
      · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
          (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
        · simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by omega)
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.sub _ (by omega) (by omega)
      · rw [show D + 2 * Q + 1 = (D + 1) + 2 * Q by omega, Proof.Hmac.Common.bytesAt_add _ _ (D + 1) (2 * Q),
          Offset.add_add, show 2256 + (D + 1) = 2256 + D + 1 by omega, hb',
          bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb]
        refine congrArg (fun y => vOf L D t.mem ++ [BitVec.ofNat 8 b] ++ y) ?_
        have hdq : Spec.Sha256.bytesAt u.mem (State.addr L.d) Q = Spec.Sha256.bytesAt t.mem (State.addr L.d) Q :=
          bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega))) (by omega)
        rw [hdq]
        refine congrArg (Spec.Sha256.bytesAt t.mem (State.addr L.d) Q ++ ·) ?_
        cases wide
        · obtain ⟨_, _⟩ := hA rfl rfl
          simp only [hPart, Bool.false_eq_true, ite_false]
          exact bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hL.stk_scr (by omega) (by omega)) (by omega)
        · obtain ⟨_, _, hdn⟩ := hW rfl rfl
          simp only [hPart, ite_true]
          refine congrArg (List.replicate (Q - D) 0 ++ ·) ?_
          exact bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega))) (by omega)
    cases wide
    · obtain ⟨rfl, hk⟩ := hA rfl rfl
      simp only [Bool.false_eq_true, ite_false, hPart, show 2 * (4 * k) = 8 * k by omega]
      exact tail_ok hL hcu hD (by omega) hk
    · obtain ⟨hQD, hQD4, hdn⟩ := hW rfl rfl
      simp only [ite_true, hPart]
      exact tailW_ok hL hcu hD hD4 h4 hQD hQD4 hq hdn

end VG.Proof.Ecdsa.Rfc6979.Arm
