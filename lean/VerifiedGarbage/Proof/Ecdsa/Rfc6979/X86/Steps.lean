module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Msg
public import VerifiedGarbage.Proof.Bignum.X86.CopyBytes
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on x86 (32-bit): the steps on `K` and `V`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Steps.lean`): each HMAC with the
key `K` and `V` (both of the digest length `D`, at the start of the frame)
is HMAC's states for `K` (by `init`, then saved, or restored from the copy),
the table's `update` with `V` and, for a new `K`, with the message at
`scratch + 2256`, then `finalize` into `V` (`vfin_ok`) or `K` (`vmfin_ok`):
`V = HMAC_K(V)` from a new `K`, saving the states (`hmacVS_ok`), or from the
saved ones (`hmacVR_ok`); `K = HMAC_K(V ‖ m)` (`hmacKB_ok`). With the message
`b ‖ d ‖ h` or `b` (`msg_ok`): steps d–e and f–g (`rekeyFull_ok`) and h.3
(`rekey_ok`). They change only `scratch`, the stack below the frame, `K` and
`V` (`KVW`).

The copies of HMAC's two states are the byte loop (`cpLoop_ok`,
`Proof.Bignum.X86.copyBytes_ok`) over their 384 bytes, from `scratch` to
`scratch + 3072` (`save_ok`) and back (`restore_ok`). A state moves with its
bytes (`RfcHash.reprOK`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The byte loop -/

/-- The loop's `n > 0` bytes from `S` (in `esi`) to `D` (in `ebx`), apart,
the count in `ecx`, into a safe region: `Ctx` kept, and the bytes copied. -/
theorem cpLoop_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {S D : BitVec 32} {n : Nat} (hn : 0 < n)
    (hn32 : n < 2 ^ 32) (hS : S.toNat + n ≤ 2 ^ 32) (hD : D.toNat + n ≤ 2 ^ 32)
    (hr : InRegions (u.rd ++ u.wr) (S.setWidth 64) n) (hw : InRegions u.wr (D.setWidth 64) n)
    (hsep : Region.Disjoint ⟨S.setWidth 64, n⟩ ⟨D.setWidth 64, n⟩) (hsafe : Safe L ⟨D.setWidth 64, n⟩)
    (hsi : u.gpr .esi = S) (hbx : u.gpr .ebx = D) (hcx : u.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa Cfg.cpLoop u fun u' => Ctx L g m₀ u' ∧ Frame [⟨D.setWidth 64, n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (D.setWidth 64) n = Spec.Sha256.bytesAt u.mem (S.setWidth 64) n ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .ecx → u'.gpr r = u.gpr r) := by
  refine WP.mono_syms (Proof.Bignum.X86.copyBytes_ok u
    (Proof.Bignum.X86.copyCtx_of_regions u S D hn32 hS hD hr hw hsep) hn hsi hbx hcx) fun u' I hsy => ?_
  have hf : Frame [⟨D.setWidth 64, n⟩] u.mem u'.mem := I.frame hD
  have hk := I.rest
  have hrest : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .ecx → u'.gpr r = u.gpr r := by
    intro r h₁ h₂ h₃ h₄
    refine hk.1 r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h) <;> contradiction
  refine ⟨hc.keep (hsy := hsy) hL hk.2.1 hk.2.2 (hk.1 .esp (by decide)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsafe), hf, ?_, hrest⟩
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have e := I.copied j hj
  rw [Proof.Bignum.X86.byteAddr_add (by omega), Proof.Bignum.X86.byteAddr_add (by omega)] at e
  exact e

/-! ## The copies of HMAC's states -/

/-- A copy at `scratch + 3072` of HMAC's inner and outer states for the block key `k0`. -/
def SavedB (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (k0 : List Byte) : Prop :=
  P.ok.hH.SH.Repr m (L.scr + BitVec.ofNat 64 3072) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
    P.ok.hH.SH.Repr m (L.scr + BitVec.ofNat 64 3264) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- The copy's region. -/
abbrev SaveR {dn : Nat} (L : Lay dn) : Region := ⟨L.scr + BitVec.ofNat 64 3072, 384⟩

theorem state_le (P : RfcHash) : P.ok.hH.SH.stateBytes ≤ 192 := by rw [P.ok.hH.hS]; nums

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
  refine ⟨P.reprOK _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.1,
    P.reprOK _ _ _ _ _ (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))).symm

/-- The arguments of a copy of the states: `esi`, `ebx` and `ecx = 384`. -/
theorem copyArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (toSave : Bool) :
    WP isa (.block (Cfg.copyArgs toSave)) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .esi = L.sc + BitVec.ofNat 32 (if toSave then sInner else sSave) ∧
      u.gpr .ebx = L.sc + BitVec.ofNat 32 (if toSave then sSave else sInner) ∧ u.gpr .ecx = 384 := by
  have k : ∀ a b : Nat, WP isa (.block (Cfg.scr .esi a ++ Cfg.scr .ebx b ++ ([.mov .ecx (.imm 384)] : List Instr))) t
      fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .esi = L.sc + BitVec.ofNat 32 a ∧
        u.gpr .ebx = L.sc + BitVec.ofNat 32 b ∧ u.gpr .ecx = 384 := fun a b => by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (scr_ok hL hc (d := .esi) (by decide) a) fun u₁ h₁ => ?_
    refine WP.mono (scr_ok hL h₁.ctx (d := .ebx) (by decide) b) fun u₂ h₂ => ?_
    refine WP.mono (movi_ok hL h₂.ctx (d := .ecx) (by decide) 384) fun u₃ h₃ => ?_
    exact ⟨h₃.ctx, by rw [h₃.mem, h₂.mem, h₁.mem], by rw [h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val],
      by rw [h₃.keep _ (by decide), h₂.val], h₃.val⟩
  cases toSave
  · exact k sSave sInner
  · exact k sInner sSave

/-- The copy of 384 bytes of `scratch` from `a` to `b`. -/
theorem copyS_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (toSave : Bool) {a b : Nat}
    (ha : a = if toSave then sInner else sSave) (hb : b = if toSave then sSave else sInner) :
    WP isa (.seq (.block (Cfg.copyArgs toSave)) Cfg.cpLoop) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 b, 384⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 b) 384 =
        Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 a) 384 := by
  have nc := hL.nc
  have hab : (a = 0 ∧ b = 3072) ∨ (a = 3072 ∧ b = 0) := by
    cases toSave <;> subst ha hb <;> decide
  refine WP.seq (WP.mono (copyArgs_ok hL hc toSave) fun u ⟨hcu, hmu, hsi, hbx, hcx⟩ => ?_)
  rw [← ha] at hsi
  rw [← hb] at hbx
  have ea : (L.sc + BitVec.ofNat 32 a).setWidth 64 = L.scr + BitVec.ofNat 64 a := hL.scrv (by omega)
  have eb : (L.sc + BitVec.ofNat 32 b).setWidth 64 = L.scr + BitVec.ofNat 64 b := hL.scrv (by omega)
  refine WP.mono (cpLoop_ok hL hcu (n := 384) (by decide) (by decide) (by rw [hL.scrN (by omega)]; omega)
    (by rw [hL.scrN (by omega)]; omega) (by rw [ea]; exact hcu.inScr (by omega))
    (by rw [eb]; exact hcu.inScrW (by omega))
    (by rw [ea, eb]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
    (by rw [eb]; exact safe_scr L (by omega)) hsi hbx hcx) fun u' ⟨hc', hf', hb', _⟩ => ?_
  rw [ea, eb, hmu] at *
  exact ⟨hc', hf', hb'⟩

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) :
    WP isa Cfg.save u fun u' => St P L g m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  have hle := state_le P
  refine WP.mono (copyS_ok hL hu.ctx true (a := 0) (b := 3072) rfl rfl) fun u' ⟨hc', hf', hb'⟩ => ?_
  have hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.ok.hH.SH.stateBytes,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega)
  have hin := hu.inner
  rw [List.append_nil] at hin
  refine ⟨⟨hc', hu.klen, hu.tlen, ?_, ?_⟩, ⟨?_, ?_⟩, hf'⟩
  · rw [List.append_nil]; exact P.reprOK _ _ _ _ _ (fun i hi => hst 0 (by decide) i hi) hin
  · exact P.reprOK _ _ _ _ _ (fun i hi => hst 192 (by decide) i hi) hu.outer
  · exact P.reprOK _ _ _ _ _ (fun i hi => byte_of_bytesAt hb' (by omega)) hin
  · exact P.reprOK _ _ _ _ _ (fun i hi => by
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
    (hk : k0.length = P.F.H.B) :
    WP isa Cfg.restore t fun u => St P L g m₀ k0 [] u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 0, 384⟩] t.mem u.mem ∧ SavedB P L u.mem k0 := by
  have hle := state_le P
  refine WP.mono (copyS_ok hL hc false (a := 3072) (b := 0) rfl rfl) fun u ⟨hcu, hf, hb⟩ => ?_
  refine ⟨⟨hcu, hk, by simp, ?_, ?_⟩, hf, hS.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · rw [List.append_nil]; exact P.reprOK _ _ _ _ _ (fun i hi => byte_of_bytesAt hb (by omega)) hS.1
  · exact P.reprOK _ _ _ _ _ (fun i hi => by
      have h := byte_of_bytesAt hb (i := 192 + i) (by omega)
      have e1 : L.scr + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add, Nat.zero_add]
      have e2 : L.scr + BitVec.ofNat 64 3264 + BitVec.ofNat 64 i =
          L.scr + BitVec.ofNat 64 3072 + BitVec.ofNat 64 (192 + i) := by
        rw [Offset.add_add, Offset.add_add]; congr 2; omega
      rw [e1, e2]; exact h) hS.2

/-! ## `K` and `V` -/

/-- `K` and `V` (of the hash function's output length), in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 140) P.F.H.D

/-- A copy of HMAC's states for the key `K`. -/
abbrev SavedK (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) (K : List Byte) : Prop :=
  SavedB P L m (Spec.Hmac.blockKey P.ok.hH.SH.H K)

/-- HMAC with a key is HMAC with its block key. -/
theorem mac_eq (P : RfcHash) (K t : List Byte) :
    P.mac K t = Spec.Hmac.hmacBlockKey P.ok.hH.SH.H (Spec.Hmac.blockKey P.ok.hH.SH.H K) t := rfl

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.F.H.D := by
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 204⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 204⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 204⟩, by simp, h⟩

/-- HMAC's writes, and the MAC's place `dst` (`K` or `V`), within `KVW`. -/
theorem wd_kvw {dst : Nat} (h : dst + P.F.H.D ≤ 128) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega))
    · exact .inr (Region.sub_prefix (by omega))
    · exact .inr (Offset.sub_base _ (by omega))

/-- The `D` bytes at `o` in the frame survive HMAC's writes and the MAC's at `dst`. -/
theorem kv_frame {dst : Nat} (hL : L.Ok) {m m' : Mem}
    (hf : Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩]) m m')
    {o : Nat} (ho : 76 ≤ o) (hod : o + P.F.H.D ≤ 76 + dst ∨ 76 + dst + P.F.H.D ≤ o) (hoe : o + P.F.H.D ≤ 588)
    (hdst : dst + P.F.H.D ≤ 128) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.F.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.F.H.D :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.stk_scr0 (by omega) (by decide)
    · exact Offset.disjoint_base _ ho (by nums)
    · exact Offset.disjoint _ hod (by omega) (by omega)) (by nums)

/-- What HMAC's functions write, with the MAC at `dst` in the frame, is apart from the copy. -/
theorem wd_save (hL : L.Ok) {dst : Nat} (hdst : dst + P.F.H.D ≤ 128) :
    ∀ r ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩], Region.Disjoint (SaveR L) r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact W_save hL r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hL.stk_scr (by nums) (by decide)).symm

/-- The message's bytes survive HMAC's writes. -/
theorem msg_W (hL : L.Ok) {m m' : Mem} (hf : Frame (W L) m m') {len : Nat} (hlen : 2256 + len ≤ 8192) :
    Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 2256) len = Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 2256) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hL.low_scr (by omega)).symm) (by omega)

/-- `update` with `V`, then `finalize` into the frame at `dst`: `HMAC(K₀, V)`. -/
theorem vfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {dst : Nat}
    (hdst : dst + P.F.H.D ≤ 128) :
    WP isa (.seq (cfgOf P).updV ((cfgOf P).fin 0 dst)) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (76 + dst), P.F.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (76 + dst)) P.F.H.D =
        Spec.Hmac.hmacBlockKey P.ok.hH.SH.H k0 (vOf P L u.mem) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.mono (fin_step hL hT hw (len := 0) (dst := dst) (by simp [Spec.Sha256.bytesAt]) (by decide) hdst)
    fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, hm'⟩
  exact (hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans hf'

/-- `update` with `V`, then with the message's `len` bytes, then `finalize`
into `K`: `HMAC(K₀, V ‖ m)`. -/
theorem vmfin_ok (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g m₀ k0 [] u) {len : Nat}
    (hlen : len ≤ 256) :
    WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun u' => Ctx L g m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (76 + fK), P.F.H.D⟩]) u.mem u'.mem ∧
      kOf P L u'.mem = Spec.Hmac.hmacBlockKey P.ok.hH.SH.H k0
        (vOf P L u.mem ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w ⟨hw, hfw⟩ => ?_)
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [Spec.Sha256.bytesAt]) hlen) fun w' ⟨hw', hfw'⟩ => ?_)
  refine WP.mono (fin_step hL hT hw' (len := len) (dst := fK)
    (by simp [Spec.Sha256.bytesAt]) hlen (by simp only [fK]; nums)) fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, ?_⟩
  · exact ((hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hfw'.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩)).trans hf'
  · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 76) P.F.H.D = _
    rw [show L.B + BitVec.ofNat 64 76 = L.B + BitVec.ofNat 64 (76 + fK) from rfl, hm',
      show sMsg = 2256 from rfl, msg_W hL hfw (len := len) (by omega)]

/-- `V`'s and `K`'s bytes survive HMAC's writes and the copy's. -/
theorem kv_WS (hL : L.Ok) {m m' : Mem} (hW : Frame (W L ++ [SaveR L]) m m') {o : Nat} (ho : 76 ≤ o)
    (hoe : o + P.F.H.D ≤ 204) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.F.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.F.H.D :=
  bytesAt_frame hW (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_scr0 (by omega) (by decide)
      · exact Offset.disjoint_base _ ho (by nums)
    · simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by decide)) (by nums)

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (save_ok hL hu) fun u' ⟨hu', hS, hf'⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu' (dst := fV) (by simp only [fV]; nums)) fun t' ⟨hc', hf'', hm⟩ => ?_
  have hW : Frame (W L ++ [SaveR L]) t.mem u'.mem :=
    (hfu.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf'.sub fun r hr => ⟨r, List.mem_append_right _ hr, sub_refl _⟩)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 76) P.F.H.D = _
    rw [kv_frame hL hf'' (o := 76) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact kv_WS hL hW (by decide) (by nums)
  have hv : vOf P L u'.mem = vOf P L t.mem := kv_WS hL hW (by decide) (by nums)
  refine ⟨hc', ?_, hk, ?_, ?_⟩
  · refine (hW.sub fun r hr => ?_).trans (hf''.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    rcases List.mem_append.mp hr with hr | hr
    · exact wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums) r (List.mem_append_left _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + fV)) P.F.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hS.frame hf'' (wd_save hL (by simp only [fV]; nums))

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, hSu⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu (dst := fV) (by simp only [fV]; nums)) fun t' ⟨hc', hf', hm⟩ => ?_
  have hR : Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, 128⟩ ⟨L.scr + BitVec.ofNat 64 0, 384⟩ :=
    hL.stk_scr (by omega) (by decide)
  have hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 76) P.F.H.D = _
    rw [kv_frame hL hf' (o := 76) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
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
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (76 + fV)) P.F.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]; exact hSu.frame hf' (wd_save hL (by simp only [fV]; nums))

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at
`scratch + 2256`, from HMAC's states for `K` by `init` or, if `fresh` is
false, from the saved ones. -/
theorem hmacKB_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256)
    (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).hmacK fresh len) t fun t' =>
      Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem)
        (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  have post : ∀ {u : State}, St P L g m₀ (Spec.Hmac.blockKey P.ok.hH.SH.H (kOf P L t.mem)) [] u →
      ∀ {ws : List Region}, Frame ws t.mem u.mem → (∀ r ∈ ws, ∃ r' ∈ KVW L, Region.Sub r r') →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 140, P.F.H.D⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 2256, len⟩ r) →
      WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun t' =>
        Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem)
          (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
    intro u hu ws hf hk hdv hdm
    refine WP.mono (vmfin_ok hL hT hu hlen) fun t' ⟨hc', hf', hm⟩ => ⟨hc', ?_, ?_, ?_⟩
    · exact (hf.sub hk).trans (hf'.sub (wd_kvw (P := P) (dst := fK) (by simp only [fK]; nums)))
    · show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 140) P.F.H.D = _
      rw [kv_frame hL hf' (o := 140) (by decide) (.inr (by simp only [fK]; nums)) (by nums) (by simp only [fK]; nums)]
      exact bytesAt_frame hf hdv (by nums)
    · rw [hm]
      have hv : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hf hdv (by nums)
      have hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len := bytesAt_frame hf hdm (by omega)
      rw [hv, hmsg, mac_eq]
  cases fresh
  · refine WP.seq (WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, _⟩ => ?_)
    have hu' : St P L g m₀ (Spec.Hmac.blockKey P.ok.hH.SH.H (kOf P L t.mem)) [] u := hu
    refine post hu' hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
    · exact hL.stk_scr (by nums) (by decide)
    · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
    refine post hu hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨L.B, 204⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact hL.stk_scr0 (by nums) (by decide)
    · exact Offset.disjoint_base _ (by omega) (by nums)
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · exact hL.low_scr (by omega) |>.symm

/-- What the steps need of the layout: the scalars' bytes, and the table of `P`. -/
def HOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := L.q = P.Q ∧ TabL P L

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
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, hdip, hsip⟩ => ?_)
  rw [← hmp] at hS ⊢
  refine WP.seq (WP.mono (msg_ok (P := P) hL hq.1 hcp hdip hsip b full) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hsafe : Region.Disjoint ⟨L.B + BitVec.ofNat 64 76, 128⟩ ⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ :=
    hL.stk_scr (by nums) (by nums)
  have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega) (by nums))) (by nums)
  have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega) (by nums))) (by nums)
  have hSu : fresh = false → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸ (hS h).frame hfu fun r hr => by
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

end VG.Proof.Ecdsa.Rfc6979.X86
