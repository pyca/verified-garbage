import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Deterministic ECDSA on x86 (32-bit): the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Msg.lean`): `V`
copied from the frame (`head_ok`), the byte `b`, then the private key and
`h` copied (`tail_ok`), or, if `wide`, the private key, a zero word and the
digest, which leaves `h` as `Q - D` zero bytes then the digest
(`tailW_ok`).
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
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- A range of `scratch`, as the code addresses it from `scratch` in a register. -/
theorem scr_addr (hL : L.Ok) {d j : Nat} (h : d + 4 * j < 8192) :
    addr L.a3 (d + 4 * j) = L.scr + BitVec.ofNat 64 d + BitVec.ofNat 64 (4 * j) := by
  rw [addr_eq (by have := hL.nc; omega), Offset.add_add]

/-- A range of the frame, as the code addresses it from `esp`. -/
theorem fr_addr (hL : L.Ok) {o j : Nat} (h : o + 4 * j < 216 + 4 * L.e) :
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
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hSA (fun j hj => scr_addr hL (by omega)) hsep (by omega) K
    (Nat.le_refl _) u hs hdi hr fun j hj => by
      rw [Offset.add_add]; exact hc.inScrW (by omega)) fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd),
      hrd, hwr, hg, hf, hb⟩

/-- The pointers: `scratch` in `edi`, `d` in `esi`, and, if `full` and
`wide`, `digest` in `edx`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (full : Bool) :
    WP isa (.block (Cfg.msgPtrs L.wide full)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .edi = L.a3 ∧
      u.gpr .esi = L.a1 ∧ (L.wide = true → full = true → u.gpr .edx = L.a2) := by
  rw [Cfg.msgPtrs, show ([.mov .edi (argM L.wide 3), .mov .esi (argM L.wide 1)] : List Instr) =
    [.mov .edi (argM L.wide 3)] ++ [.mov .esi (argM L.wide 1)] from rfl, List.append_assoc, WP.block_append_iff]
  refine WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 3) (by omega)) fun u₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hL h₁.ctx (d := .esi) (by decide) (i := 1) (by omega)) fun u₂ h₂ => ?_
  have hdi₂ : u₂.gpr .edi = L.a3 := by rw [h₂.keep _ (by decide), h₁.val]; rfl
  cases hw : L.wide && full
  · simp only
    exact WP.block_nil ⟨h₂.ctx, by rw [h₂.mem, h₁.mem], hdi₂, h₂.val, fun h h' => by
      rw [h, h'] at hw; exact absurd hw (by decide)⟩
  · simp only [ite_true]
    refine WP.mono (arg_ok hL h₂.ctx (d := .edx) (by decide) (i := 2) (by omega)) fun u₃ h₃ =>
      ⟨h₃.ctx, by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.keep _ (by decide), hdi₂],
        by rw [h₃.keep _ (by decide), h₂.val]; rfl, fun _ _ => h₃.val⟩

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
  refine ⟨hc₂.keep (hsy := by rw [v₄.syms, v₃.syms]) hL (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr])
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

/-- `‖ d ‖ h`, `k` words each, after `D + 1` bytes, with `scratch` in `edi`
and `d` in `esi`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .edi = L.a3) (hsi : u.gpr .esi = L.a1)
    {D k : Nat} (hD : D ≤ 64) (hq : 4 * k ≤ L.q) (hk : k ≤ 12) :
    WP isa (.block (Cfg.copyN k .esi 0 .edi (2256 + D + 1) ++ Cfg.copyN k .esp fH .edi (2256 + D + 1 + 4 * k))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 8 * k⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (8 * k) =
          Spec.Sha256.bytesAt u.mem L.d (4 * k) ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 204) (4 * k) := by
  have nc := hL.nc
  have nd := hL.nd
  simp only [fH]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.a1) (SA := L.d) (src := .esi) hsi (by decide) hdi (so := 0)
    (d := 2256 + D + 1) (K := k) (by omega)
    (fun j hj => by rw [addr_eq (by omega), Nat.zero_add])
    (fun j hj => hc.inD (by omega) (by omega))
    ((hL.dc.sub_left (Region.sub_prefix (by omega))).sub_right
      (Offset.sub_base _ (show 2256 + D + 1 + 4 * k ≤ 8192 by omega))))
    fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .edi = L.a3 := (hg₂ _ (by decide)).trans hdi
  refine WP.mono (copy_ok hL hc₂ (S := L.F) (SA := L.B + BitVec.ofNat 64 204) (src := .esp) hc₂.esp (by decide)
    hdi₂ (so := 128) (d := 2256 + D + 1 + 4 * k) (K := k) (by omega) (fun j hj => fr_addr hL (by omega))
    (fun j hj => by rw [Offset.add_add]; exact hc₂.inFr (by omega) (by omega) hL)
    (hL.stk_scr (by omega) (by omega))) fun u₃ ⟨hc₃, _, _, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [show 8 * k = 4 * k + 4 * k by omega, Proof.Hmac.Common.bytesAt_add _ _ (4 * k) (4 * k), Offset.add_add,
      show 2256 + D + 1 + 4 * k = 2256 + D + 1 + 4 * k from rfl, hb₃,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d (4 * k) ++ y) ?_
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)

/-- `Q` bytes copied to `scratch + d` by `copyBytes`, with `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) (hdi : u.gpr .edi = L.a3) {so d Q : Nat} (h4 : 4 ≤ Q)
    (hd : d + Q ≤ 8192) (hSA : ∀ j, j + 4 ≤ Q → addr S (so + j) = SA + BitVec.ofNat 64 j)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 j) 4)
    (hsep : Region.Disjoint ⟨SA, Q⟩ ⟨L.scr + BitVec.ofNat 64 d, Q⟩) :
    WP isa (.block (Cfg.copyBytes Q src so .edi d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) Q = Spec.Sha256.bytesAt u.mem SA Q :=
  have nc := hL.nc
  WP.mono_syms (copyBytes_ok (by decide) hsr hSA (fun j hj => by rw [addr_eq (by omega), Offset.add_add]) hsep h4
      (by omega) hs hdi hr fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd), hg, hf, hb⟩

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

/-- A zero word at `scratch + o`, with `scratch` in `edi`. -/
theorem zeroW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .edi = L.a3) {o : Nat}
    (ho : o + 4 ≤ 8192) :
    WP isa (.block [.mov .eax (.imm 0), .store (at_ .edi o) .eax]) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 o, 4⟩] u.mem u'.mem ∧
      ∀ k ≤ 4, Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 o) k = List.replicate k 0 := by
  have nc := hL.nc
  have ea : addr L.a3 o = L.scr + BitVec.ofNat 64 o := addr_eq (by omega)
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.a3) (by rw [v₁.other .edi (by decide), hdi])
    (by rw [v₁.wr, ea]; exact hc.inScrW ho) fun u₂ v₂ => WP.block_nil ?_
  have hm : u₂.mem = u.mem.writeW (L.scr + BitVec.ofNat 64 o) (0 : BitVec 32) := by
    rw [v₂.mem, v₁.gpr, v₁.mem, ea]
  have hf : Frame [⟨L.scr + BitVec.ofNat 64 o, 4⟩] u.mem u₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr]) (by rw [v₂.gpr, v₁.other _ (by decide)]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L ho),
    fun r hr => by rw [v₂.gpr, v₁.other _ hr], hf, fun k hk => by rw [hm]; exact bytesAt_writeW_zero _ _ hk⟩

/-- `‖ d ‖ h` for two `V`s to a candidate, `Q` bytes each, after `D + 1` bytes,
with `scratch` in `edi`, `d` in `esi` and `digest` in `edx`: `h` is `Q - D`
zero bytes then the digest. -/
theorem tailW_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .edi = L.a3)
    (hsi : u.gpr .esi = L.a1) (hdx : u.gpr .edx = L.a2) {D Q : Nat} (hD : D ≤ 64) (hD4 : D % 4 = 0)
    (h4 : 4 ≤ Q) (hQD : D ≤ Q) (hQD4 : Q ≤ D + 4) (hq : Q ≤ L.q) (hdn : D ≤ dn) :
    WP isa (.block (Cfg.copyBytes Q .esi 0 .edi (2256 + D + 1) ++
      ([.mov .eax (.imm 0), .store (at_ .edi (2256 + D + 1 + Q)) .eax] : List Instr) ++
      Cfg.copyN (D / 4) .edx 0 .edi (2256 + 1 + 2 * Q))) u
      fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
          Spec.Sha256.bytesAt u.mem L.d Q ++ (List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt u.mem L.dg D) := by
  have nc := hL.nc
  have nd := hL.nd
  have ng := hL.ng
  have e4 : 4 * (D / 4) = D := by omega
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyB_ok hL hc (src := .esi) (SA := L.d) hsi (by decide) hdi (so := 0) (d := 2256 + D + 1) h4
    (by omega) (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega))
    (fun j hj => hc.inD (by omega) (by omega))
    ((hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega))))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  have hdi₁ : u₁.gpr .edi = L.a3 := (hg₁ _ (by decide)).trans hdi
  have hdx₁ : u₁.gpr .edx = L.a2 := (hg₁ _ (by decide)).trans hdx
  refine WP.mono (zeroW_ok hL hc₁ hdi₁ (o := 2256 + D + 1 + Q) (by omega)) fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .edi = L.a3 := (hg₂ _ (by decide)).trans hdi₁
  have hdx₂ : u₂.gpr .edx = L.a2 := (hg₂ _ (by decide)).trans hdx₁
  refine WP.mono (copy_ok hL hc₂ (S := L.a2) (SA := L.dg) (src := .edx) hdx₂ (by decide) hdi₂ (so := 0)
    (d := 2256 + 1 + 2 * Q) (K := D / 4) (by omega) (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega))
    (fun j hj => hc₂.inDg (by omega) (by omega))
    (by rw [e4]; exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega))))
    fun u₃ ⟨hc₃, _, _, _, hf₃, hb₃⟩ => ?_
  rw [e4] at hf₃ hb₃
  refine ⟨hc₃, ?_, ?_⟩
  · refine ((hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    all_goals simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
  · have hg₁' : Spec.Sha256.bytesAt u₁.mem L.dg D = Spec.Sha256.bytesAt u.mem L.dg D :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.gc.sub_left (Region.sub_prefix hdn)).sub_right (Offset.sub_base _ (by omega))) (by omega)
    have hg₂' : Spec.Sha256.bytesAt u₂.mem L.dg D = Spec.Sha256.bytesAt u₁.mem L.dg D :=
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
    · refine congrArg (· ++ Spec.Sha256.bytesAt u.mem L.dg D) ?_
      rw [bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      exact hb₂ _ (by omega)

/-- `h` in the message: from the frame (`Q` bytes), or, if `wide`, `Q - D`
zero bytes then the digest. -/
abbrev hPart (wide : Bool) (Q D : Nat) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  if wide then List.replicate (Q - D) 0 ++ Spec.Sha256.bytesAt m L.dg D
  else Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 204) Q

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each) at
`scratch + 2256`, for `V` of `D` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a3) (hsi : t.gpr .esi = L.a1)
    (b : Nat) (full wide : Bool) (hdx : wide = true → full = true → t.gpr .edx = L.a2) {D Q : Nat}
    (hD : D ≤ 64) (hD4 : D % 4 = 0) (h4 : 4 ≤ Q) (hQ : Q ≤ 72) (hq : Q ≤ L.q)
    (hA : full = true → wide = false → Q % 4 = 0 ∧ Q ≤ 48)
    (hW : full = true → wide = true → D ≤ Q ∧ Q ≤ D + 4 ∧ D ≤ dn) :
    WP isa (.block (Cfg.msg Q D b full wide)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, D + 2 * Q + 1⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then D + 2 * Q + 1 else D + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d Q ++ hPart wide Q D L t.mem else []) := by
  have nc := hL.nc
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hdi b hD hD4) fun u ⟨hcu, _, hf, hb⟩ =>
      ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega) (by omega)
  · simp only [Cfg.msg, ite_true, sMsg]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hdi b hD hD4) fun u ⟨hcu, hg, hf, hb⟩ => ?_
    have hdi' : u.gpr .edi = L.a3 := (hg _ (by decide)).trans hdi
    have hsi' : u.gpr .esi = L.a1 := (hg _ (by decide)).trans hsi
    -- The tail, and what it is made of, unchanged by the head.
    suffices h : WP isa (.block (if wide then
          Cfg.copyBytes Q .esi 0 .edi (2256 + D + 1) ++
            ([.mov .eax (.imm 0), .store (at_ .edi (2256 + D + 1 + Q)) .eax] : List Instr) ++
            Cfg.copyN (D / 4) .edx 0 .edi (2256 + 1 + 2 * Q)
        else Cfg.copyN (Q / 4) .esi 0 .edi (2256 + D + 1) ++ Cfg.copyN (Q / 4) .esp fH .edi (2256 + D + 1 + Q))) u
        fun u' => Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 (2256 + D + 1), 2 * Q⟩] u.mem u'.mem ∧
          Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (2256 + D + 1)) (2 * Q) =
            Spec.Sha256.bytesAt u.mem L.d Q ++ hPart wide Q D L u.mem by
      refine WP.mono h fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
      · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
          (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.sub _ (by omega) (by omega)
        · simp only [List.mem_singleton] at hr; subst hr
          exact Offset.sub _ (by omega) (by omega)
      · rw [show D + 2 * Q + 1 = (D + 1) + 2 * Q by omega, Proof.Hmac.Common.bytesAt_add _ _ (D + 1) (2 * Q),
          Offset.add_add, show 2256 + (D + 1) = 2256 + D + 1 by omega, hb',
          bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb]
        refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) D ++ [BitVec.ofNat 8 b] ++ y) ?_
        have hdq : Spec.Sha256.bytesAt u.mem L.d Q = Spec.Sha256.bytesAt t.mem L.d Q :=
          bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega))) (by omega)
        rw [hdq]
        refine congrArg (Spec.Sha256.bytesAt t.mem L.d Q ++ ·) ?_
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
    · obtain ⟨hQ4, hQ48⟩ := hA rfl rfl
      obtain ⟨K, rfl⟩ : ∃ K, Q = 4 * K := ⟨Q / 4, by omega⟩
      simp only [Bool.false_eq_true, ite_false, hPart, show 4 * K / 4 = K by omega,
        show 2 * (4 * K) = 8 * K by omega]
      exact tail_ok hL hcu hdi' hsi' hD (by omega) (by omega)
    · obtain ⟨hQD, hQD4, hdn⟩ := hW rfl rfl
      simp only [ite_true, hPart]
      exact tailW_ok hL hcu hdi' hsi' ((hg _ (by decide)).trans (hdx rfl rfl)) hD hD4 h4 hQD hQD4 hq hdn

end VG.Proof.Ecdsa.Rfc6979.X86
