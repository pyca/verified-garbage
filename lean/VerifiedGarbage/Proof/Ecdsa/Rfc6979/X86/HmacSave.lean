module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Msg
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Layout

/-!
# Deterministic ECDSA on x86-64: HMAC's states for a key, saved and restored

HMAC's two states just after `init` with the key `K` depend only on `K`, so
the code keeps a copy of them at `scratch + 3072` (`SavedK`) after an `init`
(`Cfg.hmacS`, `hmacS_ok`), and, for a later HMAC with the same `K`, copies
them back in place of `init` (`Cfg.hmacR`, `hmacR_ok`). A state moves with
its bytes (`HashOK.repr`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the key `K`. -/
def SavedK (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (K : List Byte) : Prop :=
  P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3072)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H K) Spec.Hmac.ipad) ∧
    P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3328)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H K) Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR {dn : Nat} (L : Lay dn) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 512⟩

theorem state_le (P : RfcHash) : P.H.S ≤ 256 := P.ok.hSB

/-- The bytes of `n` at `p` in `m'` are those at `q` in `m`, one by one. -/
theorem byte_of_bytesAt {m m' : Mem} {p q : Addr} {n : Nat}
    (h : Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m q n) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Sha256.bytesAt, hi] using this

/-- The copy survives memory that changed apart from it. -/
theorem SavedK.frame {m m' : Mem} {K : List Byte} (hS : SavedK P L m K) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, Region.Disjoint (SaveR L) r) : SavedK P L m' K := by
  have hle := state_le P
  refine ⟨P.ok.repr _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 256⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (256 : Nat) ≤ 2 ^ 64)
      (show i < 256 by omega)) hS.1,
    P.ok.repr _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3328, 256⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (256 : Nat) ≤ 2 ^ 64)
      (show i < 256 by omega)) hS.2⟩

/-- The key survives what the copies write in `scratch`. -/
theorem keyOf_frame_scr (hL : L.Ok) {m m' : Mem} {o n : Nat} (hon : o + n ≤ 8192)
    (hf : Frame [⟨L.scr + BitVec.ofNat 64 o, n⟩] m m') : keyOf P L m' = keyOf P L m :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hL.stk_scr (by nums) hon) (by nums)

/-- After `init`: the states copied to `scratch + 3072`, and `Inited` again
from the state after the copy. -/
theorem saveS_ok (hL : L.Ok) (hT : TabL P L) {t u : State} (hu : Inited P L g m₀ t u) :
    WP isa (.block ((cfgOf P).scrPtr ++ Cfg.copyStates true)) u fun u' =>
      Inited P L g m₀ u' u' ∧ SavedK P L u'.mem (keyOf P L t.mem) ∧ keyOf P L u'.mem = keyOf P L t.mem ∧
      Frame [SaveR L] u.mem u'.mem := by
  have hle := state_le P
  rw [WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hT hu.ctx) fun u₁ h₁ => ?_
  have hc₁ := h₁.ctx
  have hm₁ := h₁.mem
  have hd₁ := h₁.val
  rw [show Cfg.copyStates true = Cfg.copyN 128 .edi 0 .edi 3072 from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .edi) (S := L.a4) (SA := L.scr + BitVec.ofNat 64 0) hd₁ (by decide) hd₁
    (so := 0) (d := 3072) (K := 128) (by decide)
    (fun j hj => by rw [addr_eq (by have := hL.nc; omega), Offset.add_add])
    (fun j hj => by rw [Offset.add_add]; exact hc₁.inScr (by omega))
    (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u' ⟨hc', _, _, _, hf', hb'⟩ => ?_
  rw [hm₁] at hf' hb'
  have hku : keyOf P L u.mem = keyOf P L t.mem :=
    bytesAt_frame hu.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_scr0 (by nums) (by decide)
      · exact Offset.disjoint_base _ (by omega) (by nums)) (by nums)
  have hk' : keyOf P L u'.mem = keyOf P L t.mem := (keyOf_frame_scr hL (o := 3072) (n := 4 * 128) (by decide) hf').trans hku
  have hst : ∀ o, o + 256 ≤ 512 → ∀ i < P.H.S,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 256⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide : (256 : Nat) ≤ 2 ^ 64)
      (show i < 256 by omega)
  refine ⟨⟨hc', Frame.refl _ _, ?_, ?_⟩, ⟨?_, ?_⟩, hk', hf'⟩
  · rw [hk']; exact P.ok.repr _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hu.inner
  · rw [hk']; exact P.ok.repr _ _ _ _ _ (fun i hi => hst 256 (by decide) i hi) hu.outer
  · exact P.ok.repr _ _ _ _ _ (fun i hi => by
      exact byte_of_bytesAt hb' (i := i) (by omega)) hu.inner
  · exact P.ok.repr _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb' (i := 256 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 3328 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (256 + i) := by
        rw [Offset.add_add, Offset.add_add, show 3328 + i = 3072 + (256 + i) by omega]
      have e2 : L.scr + BitVec.ofNat 64 256 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (256 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      rw [e1, e2]; exact h) hu.outer

/-- The copy back: HMAC's states for the key `K` in the frame, `Inited` from
the state after it, the copy kept. -/
theorem restoreS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (keyOf P L t.mem)) :
    WP isa (.block ((cfgOf P).scrPtr ++ Cfg.copyStates false)) t fun u =>
      Inited P L g m₀ u u ∧ keyOf P L u.mem = keyOf P L t.mem ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 4 * 128⟩] t.mem u.mem ∧ SavedK P L u.mem (keyOf P L t.mem) := by
  have hle := state_le P
  rw [WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hT hc) fun u₁ h₁ => ?_
  have hc₁ := h₁.ctx
  have hm₁ := h₁.mem
  have hd₁ := h₁.val
  rw [show Cfg.copyStates false = Cfg.copyN 128 .edi 3072 .edi 0 from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .edi) (S := L.a4) (SA := L.scr + BitVec.ofNat 64 3072) hd₁ (by decide) hd₁
    (so := 3072) (d := 0) (K := 128) (by decide)
    (fun j hj => by rw [addr_eq (by have := hL.nc; omega), Offset.add_add])
    (fun j hj => by rw [Offset.add_add]; exact hc₁.inScr (by omega))
    (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u ⟨hcu, _, _, _, hf, hb⟩ => ?_
  rw [hm₁] at hf hb
  have hk : keyOf P L u.mem = keyOf P L t.mem := keyOf_frame_scr hL (o := 0) (n := 4 * 128) (by decide) hf
  refine ⟨⟨hcu, Frame.refl _ _, ?_, ?_⟩, hk, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [hk]; exact P.ok.repr _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega)) hS.1
  · rw [hk]; exact P.ok.repr _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb (i := 256 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 256 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (256 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      have e2 : L.scr + BitVec.ofNat 64 3328 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (256 + i) := by
        rw [Offset.add_add, Offset.add_add, show 3328 + i = 3072 + (256 + i) by omega]
      rw [e1, e2]; exact h) hS.2

/-- After `hmacS`: `Done`'s facts, with the copy of the states for the key
in `scratch + 3072` too. -/
structure DoneS (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t : State)
    (dv : BitVec 32) (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 3584⟩, ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (76 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len)
  saved : SavedK P L u.mem (keyOf P L t.mem)

/-- What `finalize` writes is apart from the copy. -/
theorem done_save (hL : L.Ok) {dst : Nat} (hdst : dst + P.H.D ≤ 180) :
    ∀ r ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩],
      Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))).symm
  · exact (hL.stk_scr (by nums) (by decide)).symm

/-- `HMAC_K(data)` (`hmacS`), the states for `K` copied to `scratch + 3072`
after `init`. -/
theorem hmacS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {dv : BitVec 32}
    {len dst : Nat} (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv)) (hd : DataOk L dv len)
    (hds : Region.Disjoint ⟨dv.setWidth 64, len⟩ (SaveR L)) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 180) :
    WP isa ((cfgOf P).hmacS dataA len dst) t (DoneS P L g m₀ t dv len dst) :=
  WP.seq (WP.mono (init_step hL hT hc) fun u hu => WP.seq (WP.mono (saveS_ok hL hT hu) fun u' ⟨hI, hS, hk, hf⟩ =>
    WP.seq (WP.mono (upd_step hL hT hI hdA hd hlen) fun _ hw => WP.mono (fin_step hL hT hw hlen hdst) fun t' hD => by
      have hfu : Frame [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 76⟩, SaveR L] t.mem u'.mem :=
        (hu.frame.mono fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]).trans
          (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
      have hdb : Spec.Sha256.bytesAt u'.mem (dv.setWidth 64) len = Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len :=
        bytesAt_frame hfu (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · have := hd.work hL (e := 0) (k := 2256) (by omega)
            rwa [hL.scrv (by omega), BitVec.add_zero] at this
          · rw [← hL.below_F]; exact (hd.low hL).symm
          · exact hds) (by rcases hd with ⟨o, -, h⟩ | ⟨o, -, -, h⟩ <;> omega)
      refine ⟨hD.ctx, (hfu.sub fun r hr => ?_).trans (hD.frame.sub fun r hr => ?_), ?_,
        hk ▸ hS.frame hD.frame (done_save hL hdst)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨L.scr, 3584⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨L.B, 76⟩, by simp, sub_refl _⟩
        · exact ⟨⟨L.scr, 3584⟩, by simp, Offset.sub_base _ (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨L.scr, 3584⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨L.B, 76⟩, by simp, sub_refl _⟩
        · exact ⟨_, by simp, sub_refl _⟩
      · rw [hD.mac, hk, hdb])))

/-- `HMAC_K(data)` (`hmacR`), from the copy of the states for `K`: `Done`'s
facts, the copy kept. -/
theorem hmacR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (keyOf P L t.mem))
    {dataA : List Instr} {dv : BitVec 32} {len dst : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .edx dv)) (hd : DataOk L dv len)
    (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 180) :
    WP isa ((cfgOf P).hmacR dataA len dst) t fun t' => Done P L g m₀ t dv len dst t' ∧
      SavedK P L t'.mem (keyOf P L t.mem) :=
  WP.seq (WP.mono (restoreS_ok hL hT hc hS) fun u ⟨hI, hk, hf, hS'⟩ =>
    WP.seq (WP.mono (upd_step hL hT hI hdA hd hlen) fun _ hw => WP.mono (fin_step hL hT hw hlen hdst) fun t' hD => by
      have hfs : Frame [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩] t.mem u.mem :=
        hf.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨⟨L.scr, 2256⟩, by simp, Offset.sub_base _ (by decide)⟩
      have hdb : Spec.Sha256.bytesAt u.mem (dv.setWidth 64) len = Spec.Sha256.bytesAt t.mem (dv.setWidth 64) len :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          have := hd.work hL (e := 0) (k := 4 * 128) (by decide)
          rwa [hL.scrv (by omega)] at this) (by rcases hd with ⟨o, -, h⟩ | ⟨o, -, -, h⟩ <;> omega)
      exact ⟨⟨hD.ctx, hfs.trans hD.frame, by rw [hD.mac, hk, hdb]⟩, hk ▸ hS'.frame hD.frame (done_save hL hdst)⟩))

end VG.Proof.Ecdsa.Rfc6979.X86
