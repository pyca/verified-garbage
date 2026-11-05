module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block

/-!
# Deterministic ECDSA on AArch64: the steps on `K` and `V`

Each HMAC with the key `K` and `V` (both of the digest length `D`, at the
start of the frame) is HMAC's states for `K` (by `init`, then saved, or
restored from the copy), the table's `update` with `V` and, for a new `K`,
with the message at `scratch + 2256`, then `finalize` into `V`
(`vfin_ok`) or `K` (`vmfin_ok`): `V = HMAC_K(V)` from a new `K`, saving the
states (`hmacVS_ok`), or from the saved ones (`hmacVR_ok`);
`K = HMAC_K(V ‖ m)` (`hmacKB_ok`). With the message `b ‖ d ‖ h` or `b`
(`msg_ok`): steps d–e and f–g (`rekeyFull_ok`) and h.3 (`rekey_ok`). They
change only `scratch`, the stack below the frame, `K` and `V` (`KVW`).

HMAC's two states just after `init` with the key `K` depend only on `K`, so
the code keeps a copy of them at `scratch + 3072` (`SavedB`) after an `init`
(`save_ok`), and, for a later HMAC with the same `K`, copies them back in
place of `init` (`restore_ok`). A state moves with its bytes
(`StreamOK.repr`), as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Steps.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `scratch` in `x9`. -/
theorem scrPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .x9 = L.scr ∧
      ∀ r, r ≠ .x9 → u.gpr r = t.gpr r :=
  WP.mono (ldF_ok hL hc (d := .x9) (by decide) (o := fScratch) (by simp only [fScratch]; have := L.he; omega) rfl)
    fun u h => ⟨h.ctx, h.mem, h.val.trans hc.pScr, h.keep⟩

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the block key `k0`. -/
def SavedB (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) (k0 : List Byte) : Prop :=
  P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3072) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
    P.ok.SH.Repr m (L.scr + BitVec.ofNat 64 3264) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 384⟩

theorem state_le (P : RfcHash) : P.H.P.N + P.H.P.B ≤ 192 ∧ P.H.stream.S = P.H.P.N + P.H.P.B := by
  have := P.ok.B_le; have := P.ok.N_le; exact ⟨by omega, rfl⟩

/-- The bytes of `n` at `p` in `m'` are those at `q` in `m`, one by one. -/
theorem byte_of_bytesAt {m m' : Mem} {p q : Addr} {n : Nat}
    (h : Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m q n) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Sha256.bytesAt, hi] using this

/-- The copy survives memory that changed apart from it. -/
theorem SavedB.frame {m m' : Mem} {k0 : List Byte} (hS : SavedB P L m k0) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, Region.Disjoint (SaveR L) r) : SavedB P L m' k0 := by
  obtain ⟨hle, hS'⟩ := state_le P
  refine ⟨P.ok.stream.repr _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.1,
    P.ok.stream.repr _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))).symm

/-- The arguments of the copy of 384 bytes from `scratch + a` to `scratch + d`. -/
theorem copyArgs_ok (hL : L.Ok) {a d : Nat} (ha : a < 4096) (hd : d < 4096) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block ([.ldrSp .x9 fScratch] ++ [.addImm .x .x11 .x9 a] ++ [.addImm .x .x12 .x9 d] ++
      [.movz .x .x13 (BitVec.ofNat 16 384) 0])) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
        u.gpr .x11 = L.scr + BitVec.ofNat 64 a ∧ u.gpr .x12 = L.scr + BitVec.ofNat 64 d ∧
        u.gpr .x13 = BitVec.ofNat 64 384 := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  exact WP.mono (scrPtr_ok hL hc) fun u₁ ⟨hc₁, hm₁, h9₁, _⟩ =>
    WP.mono (addImm_ok hL hc₁ (d := .x11) (by decide) h9₁ ha) fun u₂ h₂ =>
    WP.mono (addImm_ok hL h₂.ctx (d := .x12) (by decide) (by rw [h₂.keep _ (by decide), h9₁]) hd) fun u₃ h₃ =>
    WP.mono (movz_ok hL h₃.ctx (d := .x13) (by decide) (n := 384) (by decide)) fun u₄ h₄ =>
      ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, hm₁], by rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.val],
        by rw [h₄.keep _ (by decide), h₃.val], h₄.val⟩

/-- The 384 bytes at `scratch + a` copied to `scratch + d`, apart, by
`cpLoop`, from `x11 = scratch + a`, `x12 = scratch + d` and `x13 = 384`. -/
theorem copy384_ok (hL : L.Ok) {a d : Nat} (ha : a < 4096) (hd : d < 4096) (hsep : a + 384 ≤ d ∨ d + 384 ≤ a)
    (hd₂ : d + 384 ≤ 8192) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block ([.ldrSp .x9 fScratch] ++ [.addImm .x .x11 .x9 a] ++ [.addImm .x .x12 .x9 d] ++
      [.movz .x .x13 (BitVec.ofNat 16 384) 0])) Cfg.cpLoop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 d, 384⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 d) 384 =
        Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 a) 384 := by
  refine WP.seq (WP.mono (copyArgs_ok hL ha hd hc) fun u ⟨hcu, hmu, h11, h12, h13⟩ => ?_)
  have hnc := hL.nc
  refine WP.mono (cp_ok hL hcu (p := L.scr + BitVec.ofNat 64 d) (q := L.scr + BitVec.ofNat 64 a) (n := 384)
    (by decide) (by decide) h13 h12 h11 ?_ (hcu.inScrW hd₂) (safe_scr L hd₂)
    (fun i hi => by rw [Offset.add_add]; exact hcu.inScr (by omega))
    (fun i hi h => Offset.disjoint L.scr (d := a + i) (n := 1) (e := d) (k := 384) (by omega) (by omega) (by omega) _
      (by rw [← Offset.add_add]; exact Region.contains_self _ _) h))
    fun u' ⟨hc', _, hf, hb⟩ => ⟨hc', hmu ▸ hf, by rw [hb, hmu]⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa Cfg.save u fun u' => St P L g m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  obtain ⟨hle, hS'⟩ := state_le P
  refine WP.mono (copy384_ok hL (a := 0) (d := 3072) (by decide) (by decide) (by decide) (by decide)
    hu.ctx) fun u' ⟨hc', hf', hb'⟩ => ?_
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
  · rw [List.append_nil]; exact P.ok.stream.repr _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hin
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => hst 192 (by decide) i hi) hu.outer
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => byte_of_bytesAt hb' (by omega)) hin
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => by
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
    WP isa Cfg.restore t fun u => St P L g m₀ k0 [] u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩] t.mem u.mem ∧ SavedB P L u.mem k0 := by
  obtain ⟨hle, hS'⟩ := state_le P
  refine WP.mono (copy384_ok hL (a := 3072) (d := 0) (by decide) (by decide) (by decide) (by decide)
    hc) fun u ⟨hcu, hf, hb⟩ => ?_
  refine ⟨⟨hcu, hk, by simp, ?_, ?_⟩, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [List.append_nil]; exact P.ok.stream.repr _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega)) hS.1
  · exact P.ok.stream.repr _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb (i := 192 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      have e2 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega
      rw [e1, e2]; exact h) hS.2

/-- `K` and `V` (of the hash function's output length), in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 80) P.H.D

/-- A copy of HMAC's states for the key `K`. -/
abbrev SavedK (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) (K : List Byte) : Prop :=
  SavedB P L m (Spec.Hmac.blockKey P.ok.SH.H K)

theorem hash_length (P : RfcHash) (m : List Byte) : (P.ok.SH.H.hash m).length = P.H.D := by
  have := P.ok.sizes.DN
  simp only [P.ok.hash, List.length_take, Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega

/-- HMAC with a key is HMAC with its block key. -/
theorem mac_eq (P : RfcHash) (K t : List Byte) :
    P.mac K t = Spec.Hmac.hmacBlockKey P.ok.SH.H (Spec.Hmac.blockKey P.ok.SH.H K) t := rfl

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.H.D := hash_length P _

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region := [L.SCR, ⟨L.B, 144⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 144⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 144⟩, by simp, h⟩

/-- HMAC's writes, and the MAC's place `dst` (`K` or `V`), within `KVW`. -/
theorem wd_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega))
    · exact .inr (Region.sub_prefix (by omega))
    · exact .inr (Offset.sub_base _ (by omega))

/-- The `D` bytes at `o` in the frame survive HMAC's writes and the MAC's at `dst`. -/
theorem kv_frame {dst : Nat} (hL : L.Ok) {m m' : Mem}
    (hf : Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩]) m m')
    {o : Nat} (ho : 16 ≤ o) (hod : o + P.H.D ≤ 16 + dst ∨ 16 + dst + P.H.D ≤ o) (hoe : o + P.H.D ≤ 200)
    (hdst : dst + P.H.D ≤ 184) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.H.D :=
  bytesAt_frame hf (fun r hr => by
    have := L.he
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.stk_scr0 (by omega) (by decide)
    · exact Offset.disjoint_base _ ho (by anums)
    · exact Offset.disjoint _ hod (by omega) (by omega)) (by anums)

/-- What HMAC's functions write, with the MAC at `dst` in the frame, is apart from the copy. -/
theorem wd_save (hL : L.Ok) {dst : Nat} (hdst : dst + P.H.D ≤ 184) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩], Region.Disjoint (SaveR L) r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact W_save hL r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_scr (by have := L.he; anums) (by decide)).symm

/-- `V`'s `D` bytes survive HMAC's writes. -/
theorem v_W (hL : L.Ok) {m m' : Mem} (hf : Frame (W L) m m') : vOf P L m' = vOf P L m :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_scr0 (by have := L.he; anums) (by decide)
    · exact Offset.disjoint_base _ (by omega) (by anums)) (by anums)

/-- The message's bytes survive HMAC's writes. -/
theorem msg_W (hL : L.Ok) {m m' : Mem} (hf : Frame (W L) m m') {len : Nat} (hlen : 2256 + len ≤ 8192) :
    Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 2256) len = Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 2256) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hL.low_scr (by omega)).symm) (by omega)

/-- The copy survives HMAC's writes. -/
theorem saved_W (hL : L.Ok) {m m' : Mem} {k0 : List Byte} (hS : SavedB P L m k0) (hf : Frame (W L) m m') :
    SavedB P L m' k0 :=
  hS.frame hf (W_save hL)

/-- `update` with `V`, then `finalize` into the frame at `dst`: `HMAC(K₀, V)`. -/
theorem vfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {dst : Nat}
    (hdst : dst + P.H.D ≤ 184) :
    WP isa (.seq (cfgOf P).updV ((cfgOf P).fin 0 dst)) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (16 + dst)) P.H.D =
        Spec.Hmac.hmacBlockKey P.ok.SH.H k0 (vOf P L u.mem) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.mono (fin_step hL hT hw (len := 0) (dst := dst) (by simp [Spec.Sha256.bytesAt]) (by decide) hdst)
    fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, hm'⟩
  exact (hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans hf'

/-- `update` with `V`, then with the message's `len` bytes, then `finalize`
into `K`: `HMAC(K₀, V ‖ m)`. -/
theorem vmfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {len : Nat}
    (hlen : len ≤ 256) :
    WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (16 + fK), P.H.D⟩]) u.mem u'.mem ∧
      kOf P L u'.mem = Spec.Hmac.hmacBlockKey P.ok.SH.H k0
        (vOf P L u.mem ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [Spec.Sha256.bytesAt]) hlen) fun w' ⟨hw', hfw'⟩ => ?_)
  refine WP.mono (fin_step hL hT hw' (len := len) (dst := fK)
    (by simp [Spec.Sha256.bytesAt]) (by omega) (by simp only [fK]; anums)) fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, ?_⟩
  · exact ((hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hfw'.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩)).trans hf'
  · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 16) P.H.D = _
    rw [show L.B + BitVec.ofNat 64 16 = L.B + BitVec.ofNat 64 (16 + fK) from rfl, hm',
      show sMsg = 2256 from rfl, msg_W hL hfw (len := len) (by omega)]

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (save_ok hL hu) fun u' ⟨hu', hS, hf'⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu' (dst := fV) (by simp only [fV]; anums)) fun t' ⟨hc', hf'', hm⟩ => ?_
  have hW : Frame (W L ++ [SaveR L]) t.mem u'.mem :=
    (hfu.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf'.sub fun r hr => ⟨r, List.mem_append_right _ hr, sub_refl _⟩)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) P.H.D = _
    rw [kv_frame hL hf'' (o := 16) (by decide) (.inl (by simp only [fV]; anums)) (by anums) (by simp only [fV]; anums)]
    exact bytesAt_frame hW (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr0 (by have := L.he; anums) (by decide)
        · exact Offset.disjoint_base _ (by omega) (by anums)
      · simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; anums) (by decide)) (by anums)
  have hv : vOf P L u'.mem = vOf P L t.mem :=
    bytesAt_frame hW (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr0 (by have := L.he; anums) (by decide)
        · exact Offset.disjoint_base _ (by omega) (by anums)
      · simp only [List.mem_singleton] at hr; subst hr
        exact hL.stk_scr (by have := L.he; anums) (by decide)) (by anums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hW.sub fun r hr => ?_).trans (hf''.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; anums)))
    rcases List.mem_append.mp hr with hr | hr
    · exact wd_kvw (P := P) (dst := fV) (by simp only [fV]; anums) r (List.mem_append_left _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + fV)) P.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hS.frame hf'' (wd_save hL (by simp only [fV]; anums))

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, hSu⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu (dst := fV) (by simp only [fV]; anums)) fun t' ⟨hc', hf', hm⟩ => ?_
  have hR : Region.Disjoint ⟨L.B + BitVec.ofNat 64 16, 128⟩ ⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩ :=
    hL.stk_scr (by have := L.he; anums) (by decide)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) P.H.D = _
    rw [kv_frame hL hf' (o := 16) (by decide) (.inl (by simp only [fV]; anums)) (by anums) (by simp only [fV]; anums)]
    exact bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega) (by anums))) (by anums)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega) (by anums))) (by anums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hfu.sub fun r hr => ?_).trans (hf'.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; anums)))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + fV)) P.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hSu.frame hf' (wd_save hL (by simp only [fV]; anums))

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at
`scratch + 2256`, from HMAC's states for `K` by `init` or, if `fresh` is
false, from the saved ones. -/
theorem hmacKB_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256)
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).hmacK fresh len) t fun t' =>
      Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem)
        (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  have post : ∀ {u : State}, St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (kOf P L t.mem)) [] u →
      ∀ {ws : List Region}, Frame ws t.mem u.mem → (∀ r ∈ ws, ∃ r' ∈ KVW L, Region.Sub r r') →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 80, P.H.D⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 2256, len⟩ r) →
      WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun t' =>
        Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem)
          (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
    intro u hu ws hf hk hdv hdm
    refine WP.mono (vmfin_ok hL hT hu hlen) fun t' ⟨hc', hf', hm⟩ => ⟨hc', ?_, ?_, ?_⟩
    · exact (hf.sub hk).trans (hf'.sub (wd_kvw (P := P) (dst := fK) (by simp only [fK]; anums)))
    · show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 80) P.H.D = _
      rw [kv_frame hL hf' (o := 80) (by decide) (.inr (by simp only [fK]; anums)) (by anums) (by simp only [fK]; anums)]
      exact bytesAt_frame hf hdv (by anums)
    · rw [hm]
      have hv : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hf hdv (by anums)
      have hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len := bytesAt_frame hf hdm (by omega)
      rw [hv, hmsg, mac_eq]
  cases fresh
  · refine WP.seq (WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, _⟩ => ?_)
    have hu' : St P L g m₀ (Spec.Hmac.blockKey P.ok.SH.H (kOf P L t.mem)) [] u := hu
    refine post hu' hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
    · exact hL.stk_scr (by have := L.he; anums) (by decide)
    · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
    refine post hu hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨L.B, 144⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact hL.stk_scr0 (by have := L.he; anums) (by decide)
    · exact Offset.disjoint_base _ (by omega) (by anums)
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact hL.low_scr (by omega) |>.symm

/-- What the steps need of the layout: the scalars' bytes, and the table of `P`. -/
def HOk (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : Prop := L.q = P.Q ∧ TabL P L

/-- `K = HMAC_K(V ‖ m)`, then `V = HMAC_K(V)`, for the message `m = b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} {full : Bool}
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block ((cfgOf P).msg b full))
      (.seq ((cfgOf P).hmacK fresh (mlen P full)) (cfgOf P).hmacVS))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  have hT := hq.2
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, h9p, h10p, h15p⟩ => ?_)
  rw [← hmp] at hS ⊢
  refine WP.seq (WP.mono (msg_ok (P := P) hL hq.1 hcp h9p h10p h15p b full) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hsafe : Region.Disjoint ⟨L.B + BitVec.ofNat 64 16, 128⟩ ⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ :=
    hL.stk_scr (by have := L.he; anums) (by anums)
  have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega) (by anums))) (by anums)
  have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega) (by anums))) (by anums)
  have hSu : fresh = false → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸ (hS h).frame hfu fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by anums) (by anums) (by anums)
  refine WP.seq (WP.mono (hmacKB_ok (P := P) hL hT hcu (len := mlen P full)
    (by cases full <;> simp only [mlen, Bool.false_eq_true, ite_true, ite_false] <;> anums) fresh hSu)
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacVS_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv', hs'⟩ => ⟨hc', ?_, ?_, ?_, hs'⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · rw [hk', hkw, hku, hvu, hbu, List.append_assoc]
  · rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) (b : Nat)
    (hS : b ≠ 0 → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  unfold Cfg.rekeyFull
  refine WP.mono (rekey_gen (full := true) hL hq hc (decide (b = 0)) fun h => hS (by simpa using h))
    fun t' h => ?_
  simpa using h

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hq hc true (fun h => absurd h (by decide)))
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
