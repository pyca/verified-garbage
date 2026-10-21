module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Msg
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Layout

/-!
# Deterministic ECDSA on x86-64: HMAC's states for a key, saved and restored

HMAC's two states just after `init` with the key `K` depend only on `K`, so
the code keeps a copy of them at `scratch + 3072` (`SavedK`) after an `init`
(`Cfg.hmacS`, `hmacS_ok`), and, for a later HMAC with the same `K`, copies
them back in place of `init` (`Cfg.hmacR`, `hmacR_ok`). A state moves with
its bytes (`HashOK.sh_reloc`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the key `K`. -/
def SavedK (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (K : List Byte) : Prop :=
  P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3072)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H K) Spec.Hmac.ipad) ∧
    P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3264)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.ok.SH.H K) Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR {dn : Nat} (L : Lay dn) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 384⟩

theorem state_le (P : RfcHash) : P.H.P.N + P.H.P.B ≤ 192 := by
  have := P.ok.B_le; have := P.ok.N_le; omega

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
  refine ⟨P.ok.sh_reloc _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.1,
    P.ok.sh_reloc _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.2⟩

/-- The key survives what the copies write in `scratch`. -/
theorem keyOf_frame_scr (hL : L.Ok) {m m' : Mem} {o n : Nat} (hon : o + n ≤ 8192)
    (hf : Frame [⟨L.scr + BitVec.ofNat 64 o, n⟩] m m') : keyOf P L m' = keyOf P L m :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hL.stk_scr (by nums) hon) (by nums)

/-- After `init`: the states copied to `scratch + 3072`, and `Inited` again
from the state after the copy. -/
theorem save_ok (hL : L.Ok) {t u : State} (hu : Inited P L g m₀ t u) :
    WP isa (.seq (.block Cfg.scrPtr) (.block (Cfg.copyStates true))) u fun u' =>
      Inited P L g m₀ u' u' ∧ SavedK P L u'.mem (keyOf P L t.mem) ∧ keyOf P L u'.mem = keyOf P L t.mem ∧
      Frame [SaveR L] u.mem u'.mem := by
  have hle := state_le P
  refine WP.seq (WP.mono (scrPtr_ok hL hu.ctx) fun u₁ ⟨hc₁, hm₁, hd₁⟩ => ?_)
  rw [show Cfg.copyStates true = Cfg.copyN 48 .rdi sInner .rdi sSave from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .rdi) (S := L.scr) hd₁ (by decide) hd₁ (so := 0) (d := 3072) (K := 48)
    (by decide) (fun j hj => hc₁.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u' ⟨hc', _, _, _, hf', hb'⟩ => ?_
  rw [hm₁] at hf' hb'
  have hku : keyOf P L u.mem = keyOf P L t.mem :=
    bytesAt_frame hu.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_scr0 (by nums) (by decide)
      · exact Offset.disjoint_base _ (by omega) (by nums)) (by nums)
  have hk' : keyOf P L u'.mem = keyOf P L t.mem := (keyOf_frame_scr hL (o := 3072) (n := 8 * 48) (by decide) hf').trans hku
  have hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.H.P.N + P.H.P.B,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)
  refine ⟨⟨hc', Frame.refl _ _, ?_, ?_⟩, ⟨?_, ?_⟩, hk', hf'⟩
  · rw [hk']; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hu.inner
  · rw [hk']; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => hst 192 (by decide) i hi) hu.outer
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => byte_of_bytesAt hb' (by omega)) hu.inner
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb' (i := 192 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega
      have e2 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      rw [e1, e2]; exact h) hu.outer

/-- The copy back: HMAC's states for the key `K` in the frame, `Inited` from
the state after it, the copy kept. -/
theorem restore_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (keyOf P L t.mem)) :
    WP isa (.seq (.block Cfg.scrPtr) (.block (Cfg.copyStates false))) t fun u =>
      Inited P L g m₀ u u ∧ keyOf P L u.mem = keyOf P L t.mem ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩] t.mem u.mem ∧ SavedK P L u.mem (keyOf P L t.mem) := by
  have hle := state_le P
  refine WP.seq (WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, hd₁⟩ => ?_)
  rw [show Cfg.copyStates false = Cfg.copyN 48 .rdi sSave .rdi sInner from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .rdi) (S := L.scr) hd₁ (by decide) hd₁ (so := 3072) (d := 0) (K := 48)
    (by decide) (fun j hj => hc₁.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u ⟨hcu, _, _, _, hf, hb⟩ => ?_
  rw [hm₁] at hf hb
  have hk : keyOf P L u.mem = keyOf P L t.mem := keyOf_frame_scr hL (o := 0) (n := 8 * 48) (by decide) hf
  refine ⟨⟨hcu, Frame.refl _ _, ?_, ?_⟩, hk, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [hk]; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega)) hS.1
  · rw [hk]; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb (i := 192 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      have e2 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega
      rw [e1, e2]; exact h) hS.2

/-- After `hmacS`: `Done`'s facts, with the copy of the states for the key
in `scratch + 3072` too. -/
structure DoneS (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t : State) (da : Addr)
    (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame [⟨L.scr, 3456⟩, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + dst)) P.H.D =
    P.mac (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)
  saved : SavedK P L u.mem (keyOf P L t.mem)

/-- What `finalize` writes is apart from the copy. -/
theorem done_save (hL : L.Ok) {dst : Nat} (hdst : dst + P.H.D ≤ 168) :
    ∀ r ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩],
      Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))).symm
  · exact (hL.stk_scr (by nums) (by decide)).symm

/-- `HMAC_K(data)` (`hmacS`), the states for `K` copied to `scratch + 3072`
after `init`. -/
theorem hmacS_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {dataA : List Instr} {da : Addr} {len dst : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) (hd : DataOk L da len)
    (hds : Region.Disjoint ⟨da, len⟩ (SaveR L)) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    WP isa ((cfgOf P).hmacS dataA len dst) t (DoneS P L g m₀ t da len dst) :=
  seq_seq (init_step hL hc) fun u hu => seq_seq (save_ok hL hu) fun u' ⟨hI, hS, hk, hf⟩ =>
    seq_seq (upd_step hL hI hdA hd hlen) fun _ hw => WP.mono (fin_step hL hw hlen hdst) fun t' hD => by
      have hfu : Frame [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 24⟩, SaveR L] t.mem u'.mem :=
        (hu.frame.mono fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]).trans
          (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
      have hdb : Spec.Sha256.bytesAt u'.mem da len = Spec.Sha256.bytesAt t.mem da len :=
        bytesAt_frame hfu (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
            · exact hL.stk_scr0 (by omega) (by decide)
            · exact Offset.disjoint_base _ (by omega) (by omega)
          · exact (hd.low hL).symm
          · exact hds) (by omega)
      refine ⟨hD.ctx, (hfu.sub fun r hr => ?_).trans (hD.frame.sub fun r hr => ?_), ?_,
        hk ▸ hS.frame hD.frame (done_save hL hdst)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨L.scr, 3456⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
        · exact ⟨⟨L.scr, 3456⟩, by simp, Offset.sub_base _ (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨L.scr, 3456⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨L.B, 24⟩, by simp, sub_refl _⟩
        · exact ⟨_, by simp, sub_refl _⟩
      · rw [hD.mac, hk, hdb]

/-- `HMAC_K(data)` (`hmacR`), from the copy of the states for `K`: `Done`'s
facts, the copy kept. -/
theorem hmacR_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (keyOf P L t.mem))
    {dataA : List Instr} {da : Addr} {len dst : Nat}
    (hdA : ∀ u, Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx da)) (hd : DataOk L da len)
    (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    WP isa ((cfgOf P).hmacR dataA len dst) t fun t' => Done P L g m₀ t da len dst t' ∧
      SavedK P L t'.mem (keyOf P L t.mem) :=
  seq_seq (restore_ok hL hc hS) fun u ⟨hI, hk, hf, hS'⟩ =>
    seq_seq (upd_step hL hI hdA hd hlen) fun _ hw => WP.mono (fin_step hL hw hlen hdst) fun t' hD => by
      have hfs : Frame [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩] t.mem u.mem :=
        hf.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨⟨L.scr, 2256⟩, by simp, Offset.sub_base _ (by decide)⟩
      have hdb : Spec.Sha256.bytesAt u.mem da len = Spec.Sha256.bytesAt t.mem da len :=
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hd.work hL (by decide)) (by omega)
      exact ⟨⟨hD.ctx, hfs.trans hD.frame, by rw [hD.mac, hk, hdb]⟩, hk ▸ hS'.frame hD.frame (done_save hL hdst)⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
