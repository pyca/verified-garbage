import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Deterministic ECDSA on x86 (32-bit): the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Msg.lean`): `V`
copied from the frame (`head_ok`), the byte `b`, then the private key and
`h` copied (`tail_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov byte [m], r`. -/
theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- A range of `scratch`, as the code addresses it from `scratch` in a register. -/
theorem scr_addr (hL : L.Ok) {d j : Nat} (h : d + 4 * j < 8192) :
    addr L.a3 (d + 4 * j) = L.scr + BitVec.ofNat 64 d + BitVec.ofNat 64 (4 * j) := by
  rw [addr_eq (by have := hL.nc; omega), Offset.add_add]

/-- A range of the frame, as the code addresses it from `esp`. -/
theorem fr_addr (hL : L.Ok) {o j : Nat} (h : o + 4 * j < 200) :
    addr L.F (o + 4 * j) = L.B + BitVec.ofNat 64 (76 + o) + BitVec.ofNat 64 (4 * j) := by
  rw [hL.addrF h, Offset.add_add, Nat.add_assoc]

/-- `4 K` bytes copied to `scratch + d` by `copyN`, with `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) (hdi : u.gpr .edi = L.a3) {so d K : Nat} (hd : d + 4 * K ≤ 8192)
    (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨L.scr + BitVec.ofNat 64 d, 4 * K⟩) :
    WP isa (.block (Cfg.copyN K src so .edi d)) u fun u' => Ctx L g m₀ u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) (4 * K) = Spec.Sha256.bytesAt u.mem SA (4 * K) :=
  WP.mono (copyN_ok (K := K) (by decide) hsr hSA (fun j hj => scr_addr hL (by omega)) hsep (by omega) K
    (Nat.le_refl _) u hs hdi hr fun j hj => by
      rw [Offset.add_add]; exact hc.inScrW (by omega)) fun u' ⟨hrd, hwr, hg, hf, hb⟩ =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd),
      hrd, hwr, hg, hf, hb⟩

/-- The pointers: `scratch` in `edi`, `d` in `esi`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .edi = L.a3 ∧
      u.gpr .esi = L.a1 := by
  rw [Cfg.msgPtrs, show ([.mov .edi (argM 3), .mov .esi (argM 1)] : List Instr) =
    [.mov .edi (argM 3)] ++ [.mov .esi (argM 1)] from rfl, WP.block_append_iff]
  refine WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 3) (by omega)) fun u₁ h₁ => ?_
  refine WP.mono (arg_ok hL h₁.ctx (d := .esi) (by decide) (i := 1) (by omega)) fun u₂ h₂ => ?_
  exact ⟨h₂.ctx, by rw [h₂.mem, h₁.mem], by rw [h₂.keep _ (by decide), h₁.val]; rfl, h₂.val⟩

/-- `V ‖ b`, for `V` of `D` bytes, with `scratch` in `edi`. -/
theorem head_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a3) (b : Nat) {D : Nat}
    (hD : D ≤ 64) (hD4 : D % 4 = 0) :
    WP isa (.block (Cfg.copyN (D / 4) .esp fV .edi sMsg ++
      ([.mov .eax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .edi (sMsg + D)) .al] : List Instr))) t fun u =>
      Ctx L g m₀ u ∧ (∀ r, r ≠ .eax → u.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 1⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] := by
  have e4 : 4 * (D / 4) = D := by omega
  have nc := hL.nc
  simp only [fV, sMsg]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.F) (SA := L.B + BitVec.ofNat 64 140) (src := .esp) hc.esp (by decide) hdi
    (so := 64) (d := 2256) (K := D / 4) (by omega) (fun j hj => fr_addr hL (by omega))
    (fun j hj => by rw [Offset.add_add]; exact hc.inFr (by omega) (by omega) hL)
    (hL.stk_scr (by omega) (by omega))) fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  rw [e4] at hf₂ hb₂
  have hdi₂ : u₂.gpr .edi = L.a3 := (hg₂ _ (by decide)).trans hdi
  have ea : addr L.a3 (2256 + D) = L.scr + BitVec.ofNat 64 (2256 + D) := addr_eq (by omega)
  refine wp_movi fun u₃ v₃ => wp_store8 (a := L.scr + BitVec.ofNat 64 (2256 + D))
    (by show addr (u₃.gpr .edi) (2256 + D) = _; rw [v₃.other .edi (by decide), hdi₂, ea])
    (by rw [v₃.wr]; exact hc₂.inScrW (o := 2256 + D) (n := 1) (by omega)) fun u₄ v₄ => WP.block_nil ?_
  have hb8 : (u₃.gpr Reg8.al.reg).setWidth 8 = BitVec.ofNat 8 b := by
    rw [show Reg8.al.reg = .eax from rfl, v₃.gpr]
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8] at v₄
  have hm₄ : u₄.mem = u₂.mem.writeW (L.scr + BitVec.ofNat 64 (2256 + D)) (BitVec.ofNat 8 b) := by
    rw [v₄.mem, v₃.mem]
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D), 1⟩] u₂.mem u₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep hL (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr])
      (by rw [v₄.gpr, v₃.other _ (by decide)]) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)),
    fun r hr => by rw [v₄.gpr, v₃.other _ hr, hg₂ r hr], ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt u₄.mem (L.scr + BitVec.ofNat 64 2256) D =
        Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 2256) D :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    rw [e₁, hb₂]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ y) ?_
    show [u₄.mem (L.scr + BitVec.ofNat 64 (2256 + D) + BitVec.ofNat 64 0)] = _
    rw [BitVec.add_zero, hm₄, WriteBytes.writeW8_apply]; simp

/-- `‖ d ‖ h`, after `D + 1` bytes, with `scratch` in `edi` and `d` in `esi`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .edi = L.a3) (hsi : u.gpr .esi = L.a1)
    {D : Nat} (hD : D ≤ 64) :
    WP isa (.block (Cfg.copyN 8 .esi 0 .edi (2256 + D + 1) ++ Cfg.copyN 8 .esp fH .edi (2256 + D + 33))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 64⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) 64 =
          Spec.Sha256.bytesAt u.mem L.d 32 ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 204) 32 := by
  have nc := hL.nc
  have nd := hL.nd
  simp only [fH]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.a1) (SA := L.d) (src := .esi) hsi (by decide) hdi (so := 0)
    (d := 2256 + D + 1) (K := 8) (by omega)
    (fun j hj => by rw [addr_eq (by omega), Nat.zero_add])
    (fun j hj => hc.inD (by omega))
    (hL.dc.sub_right (Offset.sub_base _ (by omega))))
    fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .edi = L.a3 := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copy_ok hL hc₂ (S := L.F) (SA := L.B + BitVec.ofNat 64 204) (src := .esp) hc₂.esp (by decide)
    hdi₂ (so := 128) (d := 2256 + D + 33) (K := 8) (by omega) (fun j hj => fr_addr hL (by omega))
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inFr (by omega) (by omega) hL)
    (hL.stk_scr (by omega) (by omega))) fun u₃ ⟨hc₃, _, _, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [Proof.Hmac.Common.bytesAt_add _ _ 32 32, Offset.add_add,
      show 2256 + D + 1 + 32 = 2256 + D + 33 by omega, show (32 : Nat) = 4 * 8 from rfl, hb₃,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d (4 * 8) ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`) at `scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a3) (hsi : t.gpr .esi = L.a1)
    (b : Nat) (full : Bool) {D : Nat} (hD : D ≤ 64) (hD4 : D % 4 = 0) :
    WP isa (.block (Cfg.msg D b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 65⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then D + 65 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d 32 ++ Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 204) 32
          else []) := by
  have nc := hL.nc
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hdi b hD hD4) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega) (by omega)
  · simp only [Cfg.msg, ite_true, sMsg]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hdi b hD hD4) fun u ⟨hcu, hg, hf, hb⟩ =>
      WP.mono (tail_ok hL hcu ((hg _ (by decide)).trans hdi) ((hg _ (by decide)).trans hsi) hD)
      fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
    · rw [show D + 65 = (D + 1) + 64 by omega, Proof.Hmac.Common.bytesAt_add _ _ (D + 1) 64, Offset.add_add,
        show 2256 + (D + 1) = 2256 + D + 1 by omega, hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb]
      refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] ++ y) ?_
      rw [bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.dc.sub_right (Offset.sub_base _ (by omega))) (by omega),
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by omega) (by omega)) (by omega)]

end VG.Proof.Ecdsa.Rfc6979.X86
