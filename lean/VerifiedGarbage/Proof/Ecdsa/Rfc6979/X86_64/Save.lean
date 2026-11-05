module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy

/-!
# Deterministic ECDSA on x86-64: HMAC's states for a key, saved and restored

HMAC's two states just after `init` with the key `K` depend only on `K`, so
the code keeps a copy of them at `scratch + 3072` (`SavedB`) after an `init`
(`save_ok`), and, for a later HMAC with the same `K`, copies them back in
place of `init` (`restore_ok`). A state moves with its bytes
(`HashOK.sh_reloc`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `scratch` in `rdi`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      ∀ r, r ≠ .rdi → u.gpr r = t.gpr r :=
  WP.mono (ldF_ok hL hc (d := .rdi) (by decide) (o := fScratch) (by simp only [fScratch]; have := L.he; omega))
    fun u h => ⟨h.ctx, h.mem, h.val.trans hc.pScr, h.keep⟩

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the block key `k0`. -/
def SavedB (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (k0 : List Byte) : Prop :=
  P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3072) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
    P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3264) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

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
theorem SavedB.frame {m m' : Mem} {k0 : List Byte} (hS : SavedB P L m k0) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, Region.Disjoint (SaveR L) r) : SavedB P L m' k0 := by
  have hle := state_le P
  refine ⟨P.ok.sh_reloc _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.1,
    P.ok.sh_reloc _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))).symm

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa (.block Cfg.save) u fun u' => St P L g m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  have hle := state_le P
  rw [Cfg.save, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hu.ctx) fun u₁ ⟨hc₁, hm₁, hd₁, _⟩ => ?_
  rw [show Cfg.copyStates true = Cfg.copyN 48 .rdi sInner .rdi sSave from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .rdi) (S := L.scr) hd₁ (by decide) hd₁ (so := 0) (d := 3072) (K := 48)
    (by decide) (fun j hj => hc₁.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u' ⟨hc', _, _, _, hf', hb'⟩ => ?_
  rw [hm₁] at hf' hb'
  have hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.H.P.N + P.H.P.B,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)
  have hin := hu.inner
  rw [List.append_nil] at hin
  refine ⟨⟨hc', hu.klen, hu.tlen, ?_, ?_⟩, ⟨?_, ?_⟩, hf'⟩
  · rw [List.append_nil]; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hin
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => hst 192 (by decide) i hi) hu.outer
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => byte_of_bytesAt hb' (by omega)) hin
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb' (i := 192 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega
      have e2 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      rw [e1, e2]; exact h) hu.outer

/-- The copy back: HMAC's states for the block key `k0`, and the copy kept. -/
theorem restore_ok (hL : L.Ok) {k0 : List Byte} {t : State} (hc : Ctx L g m₀ t) (hS : SavedB P L t.mem k0)
    (hk : k0.length = P.H.P.B) :
    WP isa (.block Cfg.restore) t fun u => St P L g m₀ k0 [] u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩] t.mem u.mem ∧ SavedB P L u.mem k0 := by
  have hle := state_le P
  rw [Cfg.restore, WP.block_append_iff]
  refine WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, hd₁, _⟩ => ?_
  rw [show Cfg.copyStates false = Cfg.copyN 48 .rdi sSave .rdi sInner from rfl]
  refine WP.mono (copy_ok hL hc₁ (src := .rdi) (S := L.scr) hd₁ (by decide) hd₁ (so := 3072) (d := 0) (K := 48)
    (by decide) (fun j hj => hc₁.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    fun u ⟨hcu, _, _, _, hf, hb⟩ => ?_
  rw [hm₁] at hf hb
  refine ⟨⟨hcu, hk, by simp, ?_, ?_⟩, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [List.append_nil]; exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega)) hS.1
  · exact P.ok.sh_reloc _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb (i := 192 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      have e2 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega
      rw [e1, e2]; exact h) hS.2

end VG.Proof.Ecdsa.Rfc6979.X86_64
