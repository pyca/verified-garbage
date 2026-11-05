module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: the steps on `K` and `V`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Steps.lean`): each HMAC with the
key `K` and `V` (both of the digest length `D`, at the start of the frame)
is HMAC's states for `K` (by `init`, then saved, or restored from the copy),
the table's `update` with `V` and, for a new `K`, with the message at
`scratch + 2256`, then `finalize` into `V` (`vfin_ok`) or `K` (`vmfin_ok`):
`V = HMAC_K(V)` from a new `K`, saving the states (`hmacVS_ok`), or from the
saved ones (`hmacVR_ok`); `K = HMAC_K(V ‖ m)` (`hmacKB_ok`). With the
message `b ‖ d ‖ h` or `b` (`msg_ok`): steps d–e and f–g (`rekeyFull_ok`)
and h.3 (`rekey_ok`). They change only `scratch`, the stack below the frame,
`K` and `V` (`KVW`).

HMAC's two states just after `init` with the key `K` depend only on `K`, so
the code keeps a copy of them at `scratch + 3072` (`SavedB`) after an `init`
(`save_ok`), and, for a later HMAC with the same `K`, copies them back in
place of `init` (`restore_ok`). A state moves with its hash value
(`HashOK.reloc`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Impl.RsaOaep.PPC64LE (copyLoop)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the block key `k0`. -/
def SavedB (P : RfcHash) (L : Lay dn) (m : Mem) (k0 : List Byte) : Prop :=
  P.v.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3072) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
    P.v.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3264) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR (L : Lay dn) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 384⟩

theorem n_le (P : RfcHash) : P.v.H.N ≤ 192 := by
  have := P.sizes.1; simp only [Impl.Hmac.Stream.PPC64LE.Hash.S] at this; omega

/-- The bytes of `n` at `p` in `m'` are those at `q` in `m`, one by one. -/
theorem byte_of_bytesAt {m m' : Mem} {p q : Addr} {n : Nat}
    (h : Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m q n) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Sha256.bytesAt, hi] using this

theorem pad_mod {k0 : List Byte} (hk : k0.length = P.v.H.B) (p : Byte) :
    (Spec.Hmac.xorPad k0 p).length % P.v.H.B = 0 := by
  rw [xorPad_length, hk, Nat.mod_self]

/-- The copy survives memory that changed apart from it. -/
theorem SavedB.frame {m m' : Mem} {k0 : List Byte} (hk : k0.length = P.v.H.B) (hS : SavedB P L m k0)
    {ws : List Region} (hf : Frame ws m m') (hd : ∀ r ∈ ws, Region.Disjoint (SaveR L) r) : SavedB P L m' k0 := by
  have hle := n_le P
  refine ⟨P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.1,
    P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))).symm

/-- `HMAC`'s states, as copied from `src` to `dst` (`384` bytes). -/
theorem states_moved {m m' : Mem} {src dst : Nat} {k0 : List Byte} (hk : k0.length = P.v.H.B)
    (hb : Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 dst) (8 * 48) =
      Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 src) (8 * 48))
    (hi : P.v.ok.SH.Repr m (L.scr + BitVec.ofNat 64 src) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad))
    (ho : P.v.ok.SH.Repr m (L.scr + BitVec.ofNat 64 (src + 192)) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    P.v.ok.SH.Repr m' (L.scr + BitVec.ofNat 64 dst) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
      P.v.ok.SH.Repr m' (L.scr + BitVec.ofNat 64 (dst + 192)) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) := by
  have hle := n_le P
  refine ⟨P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => byte_of_bytesAt hb (by omega)) hi,
    P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => ?_) ho⟩
  have h := byte_of_bytesAt hb (i := 192 + i) (by omega)
  rw [Offset.add_add, Offset.add_add, ← Nat.add_assoc, ← Nat.add_assoc] at h
  rw [Offset.add_add, Offset.add_add]; exact h

/-- The copy's arguments: from `scratch + src` to `scratch + dst`, 384 bytes. -/
theorem copyArgs_ok (hL : L.Ok) {src dst : Nat} (hs : src < 2 ^ 15) (hd : dst < 2 ^ 15) {t : State}
    (hc : Ctx L g lr m₀ t) :
    WP isa (.block (Cfg.scrBase ++ [.addi .r4 .r12 src, .addi .r5 .r12 dst, .li .r6 384])) t fun u =>
      Ctx L g lr m₀ u ∧ u.mem = t.mem ∧ u.gpr .r4 = L.scr + BitVec.ofNat 64 src ∧
        u.gpr .r5 = L.scr + BitVec.ofNat 64 dst ∧ u.gpr .r6 = BitVec.ofNat 64 384 :=
  WP.of_syms (scrBase_ok hc fun u₁ k₁ m₁ _ s₁ =>
    stepAddi (by decide) hs fun u₂ k₂ m₂ v₂ => stepAddi (by decide) hd fun u₃ k₃ m₃ v₃ =>
      stepLi (by decide) fun u₄ k₄ m₄ v₄ => wp_nil fun hsy => by
        have K : Kp [.r11, .r12, .r4, .r5, .r6] t u₄ := ((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono
        have hm : u₄.mem = t.mem := by rw [m₄, m₃, m₂, m₁]
        exact ⟨hc.kp hL K hm hsy, hm, by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, s₁],
          by rw [k₄.gpr _ (by decide), v₃, k₂.gpr _ (by decide), s₁], by rw [v₄]⟩)

/-- The copy of `scratch + src` to `scratch + dst`, 384 bytes, by the byte loop. -/
theorem copy384_ok (hL : L.Ok) {src dst : Nat} (hs : src < 2 ^ 15) (hd : dst < 2 ^ 15)
    (hsd : src + 384 ≤ dst ∨ dst + 384 ≤ src) (hse : src + 384 ≤ 8192) (hde : dst + 384 ≤ 8192) {t : State}
    (hc : Ctx L g lr m₀ t) :
    WP isa (.seq (.block (Cfg.scrBase ++ [.addi .r4 .r12 src, .addi .r5 .r12 dst, .li .r6 384])) copyLoop) t
      fun u => Ctx L g lr m₀ u ∧ Frame [⟨L.scr + BitVec.ofNat 64 dst, 8 * 48⟩] t.mem u.mem ∧
        Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 dst) (8 * 48) =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 src) (8 * 48) := by
  have hnc := hL.nc
  refine WP.seq (WP.mono (copyArgs_ok hL hs hd hc) fun u ⟨hu, hm, h4, h5, h6⟩ => ?_)
  refine WP.mono (cp_ok hL hu (n := 384) (by decide) (by decide) h4 h5 h6
    (fun i hi => by rw [Offset.add_add]; exact hu.inScrW (by omega))
    (safe_scr L (by omega))
    (fun i hi => by rw [Offset.add_add]; exact hu.inScr (by omega))
    (Offset.disjoint _ hsd (by omega) (by omega))
    (by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)) fun u' ⟨hc', _, hf, hb⟩ => ?_
  rw [hm] at hf hb
  exact ⟨hc', hf, hb⟩

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g lr m₀ k0 [] u) :
    WP isa Cfg.save u fun u' => St P L g lr m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  have hle := n_le P
  show WP isa (.seq (.block (Cfg.scrBase ++ [.addi .r4 .r12 0, .addi .r5 .r12 3072, .li .r6 384])) copyLoop) _ _
  refine WP.mono (copy384_ok (src := 0) (dst := 3072) hL (by decide) (by decide) (by decide) (by decide)
    (by decide) hu.ctx) fun u' ⟨hc', hf', hb'⟩ => ?_
  have hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.v.H.N,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)
  have hin := hu.inner
  rw [List.append_nil] at hin
  have hmv := states_moved (L := L) (m := u.mem) (m' := u'.mem) (src := 0) (dst := 3072) hu.klen hb' hin hu.outer
  refine ⟨⟨hc', hu.klen, hu.tlen, ?_, ?_⟩, hmv, hf'⟩
  · rw [List.append_nil]; exact P.v.ok.reloc _ _ _ _ _ (pad_mod hu.klen _) (fun i hi => hst 0 (by decide) i hi) hin
  · exact P.v.ok.reloc _ _ _ _ _ (pad_mod hu.klen _) (fun i hi => hst 192 (by decide) i hi) hu.outer

/-- The copy back: HMAC's states for the block key `k0`, and the copy kept. -/
theorem restore_ok (hL : L.Ok) {k0 : List Byte} {t : State} (hc : Ctx L g lr m₀ t) (hS : SavedB P L t.mem k0)
    (hk : k0.length = P.v.H.B) :
    WP isa Cfg.restore t fun u => St P L g lr m₀ k0 [] u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩] t.mem u.mem ∧ SavedB P L u.mem k0 := by
  show WP isa (.seq (.block (Cfg.scrBase ++ [.addi .r4 .r12 3072, .addi .r5 .r12 0, .li .r6 384])) copyLoop) _ _
  refine WP.mono (copy384_ok (src := 3072) (dst := 0) hL (by decide) (by decide) (by decide) (by decide)
    (by decide) hc) fun u ⟨hc', hf, hb⟩ => ?_
  have hmv := states_moved (L := L) (m := t.mem) (m' := u.mem) (src := 3072) (dst := 0) hk hb hS.1 hS.2
  refine ⟨⟨hc', hk, by simp, by rw [List.append_nil]; exact hmv.1, hmv.2⟩, hf, hS.frame hk hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩

/-- `K` and `V` (of the hash function's output length), in the frame. -/
abbrev kOf (P : RfcHash) (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 192) P.v.H.D

/-- A copy of HMAC's states for the key `K`. -/
abbrev SavedK (P : RfcHash) (L : Lay dn) (m : Mem) (K : List Byte) : Prop :=
  SavedB P L m (Spec.Hmac.blockKey P.v.ok.SH.H K)

/-- HMAC with a key is HMAC with its block key. -/
theorem mac_eq (P : RfcHash) (K t : List Byte) :
    P.mac K t = Spec.Hmac.hmacBlockKey P.v.ok.SH.H (Spec.Hmac.blockKey P.v.ok.SH.H K) t := rfl

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.v.H.D := P.v.ok.hashLen _

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 256⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 256⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 256⟩, by simp, h⟩

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- HMAC's writes, and the MAC's place `dst` (`K` or `V`), within `KVW`. -/
theorem wd_kvw {dst : Nat} (h : 96 + dst + P.v.H.D ≤ 256) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega))
    · exact .inr (Region.sub_prefix (by omega))
    · exact .inr (Offset.sub_base _ (by omega))

/-- The `D` bytes at `o` in the frame survive HMAC's writes and the MAC's at `dst`. -/
theorem kv_frame {dst : Nat} (hL : L.Ok) {m m' : Mem}
    (hf : Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩]) m m')
    {o : Nat} (ho : 96 ≤ o) (hod : o + P.v.H.D ≤ 96 + dst ∨ 96 + dst + P.v.H.D ≤ o) (hoe : o + P.v.H.D ≤ 736)
    (hdst : 96 + dst + P.v.H.D ≤ 736) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.v.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.v.H.D :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.stk_scr0 hoe (by decide)
    · exact Offset.disjoint_base _ ho (by nums)
    · exact Offset.disjoint _ hod (by omega) (by omega)) (by nums)

/-- What HMAC's functions write, with the MAC at `dst` in the frame, is apart from the copy. -/
theorem wd_save (hL : L.Ok) {dst : Nat} (hdst : 96 + dst + P.v.H.D ≤ 736) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩], Region.Disjoint (SaveR L) r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact W_save hL r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_scr hdst (by decide)).symm

/-- The message's bytes survive HMAC's writes. -/
theorem msg_W (hL : L.Ok) {m m' : Mem} (hf : Frame (W L) m m') {len : Nat} (hlen : 2256 + len ≤ 8192) :
    Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 2256) len = Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 2256) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hL.low_scr (by omega)).symm) (by omega)

/-- `update` with `V`, then `finalize` into the frame at `dst`: `HMAC(K₀, V)`. -/
theorem vfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g lr m₀ k0 [] u) {dst : Nat}
    (hdst : 32 ≤ dst ∧ dst + 64 ≤ 176) :
    WP isa (.seq (cfgOf P).updV ((cfgOf P).fin 0 dst)) u fun u' => Ctx L g lr m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (96 + dst)) P.v.H.D =
        Spec.Hmac.hmacBlockKey P.v.ok.SH.H k0 (vOf P L u.mem) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.mono (fin_step hL hT hw (len := 0) (dst := dst) (by simp [Spec.Sha256.bytesAt]) (by decide) hdst)
    fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, hm'⟩
  exact (hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans hf'

/-- `update` with `V`, then with the message's `len` bytes, then `finalize`
into `K`: `HMAC(K₀, V ‖ m)`. -/
theorem vmfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g lr m₀ k0 [] u) {len : Nat}
    (hlen : len ≤ 256) :
    WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun u' =>
      Ctx L g lr m₀ u' ∧ Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (96 + fK), P.v.H.D⟩]) u.mem u'.mem ∧
      kOf P L u'.mem = Spec.Hmac.hmacBlockKey P.v.ok.SH.H k0
        (vOf P L u.mem ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [Spec.Sha256.bytesAt]) hlen) fun w' ⟨hw', hfw'⟩ => ?_)
  refine WP.mono (fin_step hL hT hw' (len := len) (dst := fK)
    (by simp [Spec.Sha256.bytesAt]) (by omega) (by simp only [fK]; omega)) fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, ?_⟩
  · exact ((hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hfw'.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩)).trans hf'
  · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 128) P.v.H.D = _
    rw [show L.B + BitVec.ofNat 64 128 = L.B + BitVec.ofNat 64 (96 + fK) from rfl, hm',
      show sMsg = 2256 from rfl, msg_W hL hfw (len := len) (by omega)]

/-- `V` and `K` survive a frame of the HMAC's writes and the copy. -/
theorem kv_save (hL : L.Ok) {m m' : Mem} (hW : Frame (W L ++ [SaveR L]) m m') {o : Nat} (ho : 96 ≤ o)
    (hoe : o + P.v.H.D ≤ 736) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.v.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.v.H.D :=
  bytesAt_frame hW (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_scr0 hoe (by decide)
      · exact Offset.disjoint_base _ ho (by nums)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr hoe (by decide)) (by nums)

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (save_ok hL hu) fun u' ⟨hu', hS, hf'⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu' (dst := fV) (by simp only [fV]; omega)) fun t' ⟨hc', hf'', hm⟩ => ?_
  have hW : Frame (W L ++ [SaveR L]) t.mem u'.mem :=
    (hfu.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf'.sub fun r hr => ⟨r, List.mem_append_right _ hr, sub_refl _⟩)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 128) P.v.H.D = _
    rw [kv_frame hL hf'' (o := 128) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact kv_save hL hW (by decide) (by nums)
  have hv : vOf P L u'.mem = vOf P L t.mem := kv_save hL hW (by decide) (by nums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hW.sub fun r hr => ?_).trans (hf''.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    rcases List.mem_append.mp hr with hr | hr
    · exact wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums) r (List.mem_append_left _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (96 + fV)) P.v.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]
    exact hS.frame (blockKey_length (keyOf_length _)) hf'' (wd_save hL (by simp only [fV]; nums))

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, hSu⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu (dst := fV) (by simp only [fV]; omega)) fun t' ⟨hc', hf', hm⟩ => ?_
  have hR : Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, 128⟩ ⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩ :=
    hL.stk_scr (by omega) (by decide)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 128) P.v.H.D = _
    rw [kv_frame hL hf' (o := 128) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega) (by nums))) (by nums)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega) (by nums))) (by nums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hfu.sub fun r hr => ?_).trans (hf'.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (96 + fV)) P.v.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hSu.frame (blockKey_length (keyOf_length _)) hf' (wd_save hL (by simp only [fV]; nums))

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at
`scratch + 2256`, from HMAC's states for `K` by `init` or, if `fresh` is
false, from the saved ones. -/
theorem hmacKB_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) {len : Nat} (hlen : len ≤ 256)
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).hmacK fresh len) t fun t' =>
      Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem)
        (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  have post : ∀ {u : State}, St P L g lr m₀ (Spec.Hmac.blockKey P.v.ok.SH.H (kOf P L t.mem)) [] u →
      ∀ {ws : List Region}, Frame ws t.mem u.mem → (∀ r ∈ ws, ∃ r' ∈ KVW L, Region.Sub r r') →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 192, P.v.H.D⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 2256, len⟩ r) →
      WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun t' =>
        Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem)
          (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
    intro u hu ws hf hk hdv hdm
    refine WP.mono (vmfin_ok hL hT hu hlen) fun t' ⟨hc', hf', hm⟩ => ⟨hc', ?_, ?_, ?_⟩
    · exact (hf.sub hk).trans (hf'.sub (wd_kvw (P := P) (dst := fK) (by simp only [fK]; nums)))
    · show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 192) P.v.H.D = _
      rw [kv_frame hL hf' (o := 192) (by decide) (.inr (by simp only [fK]; nums)) (by nums) (by simp only [fK]; nums)]
      exact bytesAt_frame hf hdv (by nums)
    · rw [hm]
      have hv : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hf hdv (by nums)
      have hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len := bytesAt_frame hf hdm (by omega)
      rw [hv, hmsg, mac_eq]
  cases fresh
  · refine WP.seq (WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, _⟩ => ?_)
    have hu' : St P L g lr m₀ (Spec.Hmac.blockKey P.v.ok.SH.H (kOf P L t.mem)) [] u := hu
    refine post hu' hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
    · exact hL.stk_scr (by nums) (by decide)
    · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
    refine post hu hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨L.B, 256⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact hL.stk_scr0 (by nums) (by decide)
    · exact Offset.disjoint_base _ (by omega) (by nums)
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact hL.low_scr (by omega) |>.symm

/-- What the steps need of the layout: the scalars' bytes, and the table of `P`. -/
def HOk (P : RfcHash) (L : Lay dn) : Prop := L.q = P.Q ∧ TabL P L

/-- `K = HMAC_K(V ‖ m)`, then `V = HMAC_K(V)`, for the message `m = b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {b : Nat} (hb : b < 2 ^ 15)
    {full : Bool} (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block ((cfgOf P).msg b full))
      (.seq ((cfgOf P).hmacK fresh (mlen P full)) (cfgOf P).hmacVS))) t
      fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  have hT := hq.2
  refine WP.seq (WP.mono (msgPtrs_ok hL hc) fun p ⟨hcp, hmp, _, h11, h9, h10⟩ => ?_)
  rw [← hmp] at hS ⊢
  refine WP.seq (WP.mono (msg_ok (P := P) hL hq.1 hcp h11 h9 h10 hb full) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hsafe : Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, 128⟩ ⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ :=
    hL.stk_scr (by omega) (by nums)
  have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega) (by nums))) (by nums)
  have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega) (by nums))) (by nums)
  have hSu : fresh = false → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸
    (hS h).frame (blockKey_length (keyOf_length _)) hfu fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by nums) (by nums) (by nums)
  refine WP.seq (WP.mono (hmacKB_ok (P := P) hL hT hcu (len := mlen P full)
    (by cases full <;> simp only [mlen, Bool.false_eq_true, ite_true, ite_false] <;> nums) fresh hSu)
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacVS_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv', hs'⟩ => ⟨hc', ?_, ?_, ?_, hs'⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by nums)))).trans hfw).trans hf'
  · rw [hk', hkw, hku, hvu, hbu, List.append_assoc]
  · rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) (b : Nat) (hb : b < 2 ^ 15)
    (hS : b ≠ 0 → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  unfold Cfg.rekeyFull
  refine WP.mono (rekey_gen (full := true) hL hq hc hb (decide (b = 0)) fun h => hS (by simpa using h))
    fun t' h => ?_
  simpa using h

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hq hc (by decide) true (fun h => absurd h (by decide)))
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
