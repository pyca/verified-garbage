module
-- separate module: its proofs (the candidate loop) build in parallel with `Core`'s, which `Loop` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `Ecdsa.Rfc6979.PPC64LE.Steps`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.PPC64LE.Msg`, which only this module used -/

section

/-!
# Deterministic ECDSA on PPC64LE: the messages of steps d, f and h.3

The byte `b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`), after
the pointers (`msgPtrs_ok`): the byte, then the private key and `h`, `Q` bytes
each, copied a 32-bit word, then a byte, at a time (`copyN_ok`). HMAC's text
is `V` (`D` bytes, from the frame, the table's `update` with it), then this
message.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Hmac.Common (bytesAt_add)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- The pointers: the frame's base in `r11`, `scratch` in `r9`, `d` in `r10`. -/
theorem msgPtrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g lr m₀ u ∧ u.mem = t.mem ∧ Kp [.r9, .r10, .r11] t u ∧
      u.gpr .r11 = L.B + BitVec.ofNat 64 96 ∧ u.gpr .r9 = L.scr ∧ u.gpr .r10 = L.d := by
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  obtain hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega_using []) (by omega_using [])) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 288) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl) (hc.inFrK (k₁.mono.trans k₂.mono (rs := [.r11, .r9])) (by omega_using []) (by omega_using []))
    fun t₃ k₃ m₃ v₃ => wp_nil fun hsy => ?_
  obtain K : Kp [.r9, .r10, .r11] t t₃ := (k₁.mono.trans k₂.mono).trans k₃.mono
  obtain hm : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
  exact ⟨hc.kp hL K hm hsy, hm, K, by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb],
    by rw [k₃.gpr _ (by decide), v₂, m₁, hc.pScr], by rw [v₃, m₂, m₁, hc.pD]⟩

theorem bytesAt_byte (m : Mem) (a : Addr) (v : BitVec 8) : Spec.Sha256.bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [Spec.Sha256.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, Mem.writeW,
    Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, List.cons.injEq, and_true]
  exact BitVec.eq_of_toNat_eq (by simp)

variable {P : RfcHash}

/-- `h` in the frame. -/
abbrev hOf (P : RfcHash) (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q

/-- What follows the message's first byte: `d ‖ h` once step d wrote them. -/
abbrev tailOf (P : RfcHash) (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 (2256 + 1)) (2 * P.Q)

/-- The length of the message. -/
abbrev mlen (P : RfcHash) (full : Bool) : Nat := if full then 1 + 2 * P.Q else 1

/-- Where `h` is in the frame: `fH`, or `X`'s place if `big`. -/
theorem fHo_le (P : RfcHash) : 232 ≤ (cfgOf P).fHo ∧ (cfgOf P).fHo + P.Q ≤ 376 := by
  have := P.sizes
  simp only [Cfg.fHo, cfgOf]
  rcases Bool.eq_false_or_eq_true P.R.big with h | h <;>
    simp only [h, fX, fH, ite_true, ite_false, Bool.false_eq_true] <;> nums

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t)
    (h11 : t.gpr .r11 = L.B + BitVec.ofNat 64 96) (h9 : t.gpr .r9 = L.scr) (h10 : t.gpr .r10 = L.d)
    {b : Nat} (hb : b < 2 ^ 15) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g lr m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] ∧
      tailOf P L t'.mem = if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else tailOf P L t.mem := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hnd := hL.nd
  have hQ := P.sizes
  obtain hho := fHo_le P
  have hlen : (cfgOf P).len = P.Q := rfl
  refine WP.of_syms ?_
  simp only [Cfg.msg, List.cons_append, List.nil_append]
  -- The byte.
  refine stepLi hb fun t₃ k₃ m₃ v₃ => ?_
  refine stepStb (a := L.scr + BitVec.ofNat 64 2256) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), h9]; rfl) (by rw [k₃.wr]; exact hc.inScrW (by omega_using []))
    fun t₄ k₄ g₄ m₄ => ?_
  obtain hb₄ : Spec.Sha256.bytesAt t₄.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] := by
    rw [m₄, bytesAt_byte, v₃]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)
  obtain f₄ : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem t₄.mem := by
    rw [m₄, m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain K₄ : Kp [.r8] t t₄ := k₃.trans k₄.mono
  obtain keep : ∀ {u u' : State} {o n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      o + n ≤ o' ∨ o' + n' ≤ o → o' + n' ≤ 8192 → o + n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 o) n :=
    fun f h h₁ h₂ => bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ h (by omega_using [h₂]) (by omega_using [h₁])) (by omega_using [h₂])
  obtain keepS : ∀ {u u' : State} {p : Addr} {n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      Region.Disjoint ⟨p, n⟩ ⟨L.scr + BitVec.ofNat 64 o', n'⟩ → n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem p n :=
    fun f h hn => bytesAt_frame f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) (by omega_using [hn])
  obtain sub : ∀ {o n : Nat}, 2256 ≤ o → o + n ≤ 2256 + (1 + 2 * P.Q) →
      ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, n⟩ : Region)],
        ∃ r' ∈ [(⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ : Region)], Region.Sub r r' :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ h₁ h₂⟩
  obtain safeM : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ : Region)], Safe L r := by
    simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by nums)
  cases full
  · simp only [Bool.false_eq_true, ite_false]
    refine wp_nil fun hsy => ⟨hc.keep hL K₄.rd K₄.wr K₄.sp (fun r hr => K₄.gpr r (by
        intro h; simp at h; subst h; simp [preserved] at hr)) (f₄.sub (sub (by omega_using []) (by omega_using []))) safeM hsy,
      f₄.sub (sub (by omega_using []) (by omega_using [])), hb₄, keep f₄ (by omega_using []) (by omega_using []) (by nums)⟩
  · simp only [ite_true]
    rw [WP.block_append_iff]
    -- `d`.
    refine WP.mono (copyN_ok (S := L.d) (D := L.scr) (so := 0) (d := sMsg + 1) (n := P.Q)
      (by decide) (by decide) (by decide) (by decide)
      (by
        rw [BitVec.add_zero]
        exact (hL.dc.sub_left (Region.sub_prefix (by omega_using [hq]))).sub_right (Offset.sub_base _ (by simp only [sMsg]; nums)))
      (by nums) (by simp only [sMsg]; nums) t₄
      (by rw [K₄.gpr _ (by decide), h10]) (by rw [K₄.gpr _ (by decide), h9])
      (fun j k hjk => by rw [K₄.rd, K₄.wr, Nat.zero_add]; exact hc.inD (by omega_using [hq, hjk]) (by nums))
      (fun j k hjk => by rw [K₄.wr]; exact hc.inScrW (by simp only [sMsg]; nums)))
      fun t₅ ⟨k₅, f₅, v₅⟩ => ?_
    -- `h`.
    refine WP.mono (copyN_ok (S := L.B + BitVec.ofNat 64 96) (D := L.scr) (so := (cfgOf P).fHo)
      (d := sMsg + 1 + P.Q) (n := P.Q) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr_add]; exact hL.stk_scr (by omega_using [hho]) (by simp only [sMsg]; nums)) (by omega_using [hho])
      (by simp only [sMsg]; nums) t₅
      (by rw [k₅.gpr _ (by decide), K₄.gpr _ (by decide), h11])
      (by rw [k₅.gpr _ (by decide), K₄.gpr _ (by decide), h9])
      (fun j k hjk => by rw [k₅.rd, k₅.wr, K₄.rd, K₄.wr, fr_add]; exact hc.inFr (by omega_using [hho]) (by omega_using [hho, hjk]))
      (fun j k hjk => by rw [k₅.wr, K₄.wr]; exact hc.inScrW (by simp only [sMsg]; nums)))
      fun t₆ ⟨k₆, f₆, v₆⟩ hsy => ?_
    simp only [sMsg] at f₅ v₅ f₆ v₆
    obtain F : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t₆.mem :=
      ((f₄.sub (sub (by omega_using []) (by omega_using []))).trans (f₅.sub (sub (by omega_using []) (by omega_using [])))).trans
        (f₆.sub (sub (by omega_using []) (by omega_using [])))
    obtain K : Kp [.r8] t t₆ := (K₄.trans k₅).trans k₆
    refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
        intro h; simp at h; subst h; simp [preserved] at hr)) F safeM hsy, F, ?_, ?_⟩
    · rw [keep (o := 2256) (n := 1) f₆ (by omega_using []) (by nums) (by omega_using []),
        keep (o := 2256) (n := 1) f₅ (by omega_using []) (by nums) (by omega_using []), hb₄]
    -- `d` and `h`, as on entry.
    obtain hd₄ : Spec.Sha256.bytesAt t₄.mem L.d P.Q = Spec.Sha256.bytesAt t.mem L.d P.Q :=
      keepS f₄ ((hL.dc.sub_left (Region.sub_prefix (by omega_using [hq]))).sub_right (Offset.sub_base _ (by omega_using [])))
        (by omega_using [hQ])
    obtain hh₅ : Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q = hOf P L t.mem := by
      rw [keepS f₅ (hL.stk_scr (by omega_using [hho]) (by nums)) (by omega_using [hQ]), keepS f₄ (hL.stk_scr (by omega_using [hho]) (by omega_using []))
        (by omega_using [hQ])]
    show Spec.Sha256.bytesAt t₆.mem (L.scr + BitVec.ofNat 64 (2256 + 1)) (2 * P.Q) = _
    rw [show 2 * P.Q = P.Q + P.Q by omega_using [], bytesAt_add, Offset.add_add,
      keep (o := 2256 + 1) (n := P.Q) f₆ (by omega_using []) (by nums) (by nums), v₅, BitVec.add_zero, hd₄, v₆, fr_add, hh₅]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

end

end


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
  have := P.sizes.1; simp only [Impl.Hmac.Stream.PPC64LE.Hash.S] at this; omega_using [this]

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
  obtain hle := n_le P
  refine ⟨P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3072, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])) hS.1,
    P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 3264, 192⟩) hf
      (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega_using []) (by omega_using []))) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])) hS.2⟩

/-- What HMAC's functions write is apart from the copy. -/
theorem W_save (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint (SaveR L) r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (Offset.disjoint_base _ (by decide) (by decide))
  · exact ((hL.kc.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Offset.sub_base _ (by decide))).symm

/-- `HMAC`'s states, as copied from `src` to `dst` (`384` bytes). -/
theorem states_moved {m m' : Mem} {src dst : Nat} {k0 : List Byte} (hk : k0.length = P.v.H.B)
    (hb : Spec.Sha256.bytesAt m' (L.scr + BitVec.ofNat 64 dst) (8 * 48) =
      Spec.Sha256.bytesAt m (L.scr + BitVec.ofNat 64 src) (8 * 48))
    (hi : P.v.ok.SH.Repr m (L.scr + BitVec.ofNat 64 src) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad))
    (ho : P.v.ok.SH.Repr m (L.scr + BitVec.ofNat 64 (src + 192)) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) :
    P.v.ok.SH.Repr m' (L.scr + BitVec.ofNat 64 dst) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad) ∧
      P.v.ok.SH.Repr m' (L.scr + BitVec.ofNat 64 (dst + 192)) (Spec.Hmac.xorPad k0 Spec.Hmac.opad) := by
  obtain hle := n_le P
  refine ⟨P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => byte_of_bytesAt hb (by omega_using [hle, hi])) hi,
    P.v.ok.reloc _ _ _ _ _ (pad_mod hk _) (fun i hi => ?_) ho⟩
  obtain h := byte_of_bytesAt hb (i := 192 + i) (by omega_using [hle, hi])
  rw [Offset.add_add, Offset.add_add, ← Nat.add_assoc, ← Nat.add_assoc] at h
  rw [Offset.add_add, Offset.add_add]; exact h

/-- The copy's arguments: from `scratch + src` to `scratch + dst`, 384 bytes. -/
theorem copyArgs_ok (hL : L.Ok) {src dst : Nat} (hs : src < 2 ^ 15) (hd : dst < 2 ^ 15) {t : State}
    (hc : Ctx L g lr m₀ t) :
    WP isa (.block (Cfg.scrBase ++ ([.addi .r4 .r12 src, .addi .r5 .r12 dst, .li .r6 384] : List Instr))) t fun u =>
      Ctx L g lr m₀ u ∧ u.mem = t.mem ∧ u.gpr .r4 = L.scr + BitVec.ofNat 64 src ∧
        u.gpr .r5 = L.scr + BitVec.ofNat 64 dst ∧ u.gpr .r6 = BitVec.ofNat 64 384 :=
  WP.of_syms (scrBase_ok hc fun u₁ k₁ m₁ _ s₁ =>
    stepAddi (by decide) hs fun u₂ k₂ m₂ v₂ => stepAddi (by decide) hd fun u₃ k₃ m₃ v₃ =>
      stepLi (by decide) fun u₄ k₄ m₄ v₄ => wp_nil fun hsy => by
        obtain K : Kp [.r11, .r12, .r4, .r5, .r6] t u₄ := ((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono
        obtain hm : u₄.mem = t.mem := by rw [m₄, m₃, m₂, m₁]
        exact ⟨hc.kp hL K hm hsy, hm, by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, s₁],
          by rw [k₄.gpr _ (by decide), v₃, k₂.gpr _ (by decide), s₁], by rw [v₄]⟩)

/-- The copy of `scratch + src` to `scratch + dst`, 384 bytes, by the byte loop. -/
theorem copy384_ok (hL : L.Ok) {src dst : Nat} (hs : src < 2 ^ 15) (hd : dst < 2 ^ 15)
    (hsd : src + 384 ≤ dst ∨ dst + 384 ≤ src) (hse : src + 384 ≤ 8192) (hde : dst + 384 ≤ 8192) {t : State}
    (hc : Ctx L g lr m₀ t) :
    WP isa (.seq (.block (Cfg.scrBase ++ ([.addi .r4 .r12 src, .addi .r5 .r12 dst, .li .r6 384] : List Instr))) copyLoop) t
      fun u => Ctx L g lr m₀ u ∧ Frame [⟨L.scr + BitVec.ofNat 64 dst, 8 * 48⟩] t.mem u.mem ∧
        Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 dst) (8 * 48) =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 src) (8 * 48) := by
  have hnc := hL.nc
  refine WP.seq (WP.mono (copyArgs_ok hL hs hd hc) fun u ⟨hu, hm, h4, h5, h6⟩ => ?_)
  refine WP.mono (cp_ok hL hu (n := 384) (by decide) (by decide) h4 h5 h6
    (fun i hi => by rw [Offset.add_add]; exact hu.inScrW (by omega_using [hde, hi]))
    (safe_scr L (by omega_using [hde]))
    (fun i hi => by rw [Offset.add_add]; exact hu.inScr (by omega_using [hse, hi]))
    (Offset.disjoint _ hsd (by omega_using [hs]) (by omega_using [hd]))
    (by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_using [hde, hnc])]; omega_using [hde, hnc])) fun u' ⟨hc', _, hf, hb⟩ => ?_
  rw [hm] at hf hb
  exact ⟨hc', hf, hb⟩

/-- After `init`: the states copied to `scratch + 3072`, and `St` kept. -/
theorem save_ok (hL : L.Ok) {k0 : List Byte} {u : State} (hu : St P L g lr m₀ k0 [] u) :
    WP isa Cfg.save u fun u' => St P L g lr m₀ k0 [] u' ∧ SavedB P L u'.mem k0 ∧
      Frame [SaveR L] u.mem u'.mem := by
  obtain hle := n_le P
  show WP isa (.seq (.block (Cfg.scrBase ++ [.addi .r4 .r12 0, .addi .r5 .r12 3072, .li .r6 384])) copyLoop) _ _
  refine WP.mono (copy384_ok (src := 0) (dst := 3072) hL (by decide) (by decide) (by decide) (by decide)
    (by decide) hu.ctx) fun u' ⟨hc', hf', hb'⟩ => ?_
  obtain hst : ∀ o, o + 192 ≤ 384 → ∀ i < P.v.H.N,
      u'.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = u.mem (L.scr + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o ho i hi => Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 o, 192⟩) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [ho]) (by omega_using [])) (by decide : (192 : Nat) ≤ 2 ^ 64)
      (show i < 192 by omega_using [hle, hi])
  have hin := hu.inner
  rw [List.append_nil] at hin
  obtain hmv := states_moved (L := L) (m := u.mem) (m' := u'.mem) (src := 0) (dst := 3072) hu.klen hb' hin hu.outer
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
  obtain hmv := states_moved (L := L) (m := t.mem) (m' := u.mem) (src := 3072) (dst := 0) hk hb hS.1 hS.2
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
    · exact .inl (Region.sub_prefix (by omega_using []))
    · exact .inr (Region.sub_prefix (by omega_using []))
    · exact .inr (Offset.sub_base _ (by omega_using [h]))

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
    · exact Offset.disjoint _ hod (by omega_using [hoe]) (by omega_using [hdst])) (by nums)

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
    · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hlen])
    · exact (hL.low_scr (by omega_using [hlen])).symm) (by omega_using [hlen])

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
    (by simp [Spec.Sha256.bytesAt]) (by omega_using [hlen]) (by simp only [fK]; omega_using [])) fun u' ⟨hc', hf', hm'⟩ => ⟨hc', ?_, ?_⟩
  · exact ((hfw.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hfw'.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩)).trans hf'
  · show Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 128) P.v.H.D = _
    rw [show L.B + BitVec.ofNat 64 128 = L.B + BitVec.ofNat 64 (96 + fK) from rfl, hm',
      show sMsg = 2256 from rfl, msg_W hL hfw (len := len) (by omega_using [hlen])]

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

/-- What follows the message's first byte, kept by memory that changed apart from it. -/
theorem tail_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 (2256 + 1), 2 * P.Q⟩ r) :
    tailOf P L m' = tailOf P L m :=
  bytesAt_frame hf hd (by nums)

/-- What HMAC's functions write is apart from it. -/
theorem tail_w (hL : L.Ok) : ∀ r ∈ W L, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 (2256 + 1), 2 * P.Q⟩ r := by
  intro r hr
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by omega_using []) (by nums)
  · exact (hL.low_scr (by nums)).symm

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) ∧ tailOf P L t'.mem = tailOf P L t.mem := by
  refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (save_ok hL hu) fun u' ⟨hu', hS, hf'⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu' (dst := fV) (by simp only [fV]; omega_using [])) fun t' ⟨hc', hf'', hm⟩ => ?_
  obtain hW : Frame (W L ++ [SaveR L]) t.mem u'.mem :=
    (hfu.sub fun r hr => ⟨r, List.mem_append_left _ hr, sub_refl _⟩).trans
      (hf'.sub fun r hr => ⟨r, List.mem_append_right _ hr, sub_refl _⟩)
  obtain hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 128) P.v.H.D = _
    rw [kv_frame hL hf'' (o := 128) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact kv_save hL hW (by decide) (by nums)
  obtain hv : vOf P L u'.mem = vOf P L t.mem := kv_save hL hW (by decide) (by nums)
  have hnB := hL.nB
  refine ⟨hc', ?_, hk, ?_, ?_, ?_⟩
  · refine (hW.sub fun r hr => ?_).trans (hf''.sub (wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums)))
    rcases List.mem_append.mp hr with hr | hr
    · exact wd_kvw (P := P) (dst := fV) (by simp only [fV]; nums) r (List.mem_append_left _ hr)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
  · rw [show vOf P L t'.mem = Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (96 + fV)) P.v.H.D from rfl, hm, hv,
      mac_eq]
  · rw [hk]
    exact hS.frame (blockKey_length (keyOf_length _)) hf'' (wd_save hL (by simp only [fV]; nums))
  · have e₁ : tailOf P L t'.mem = tailOf P L u'.mem := tail_frame hf'' fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact tail_w hL r hr
      · simp only [List.mem_singleton] at hr; subst hr
        refine (hL.stk_scr ?_ ?_).symm <;> (try simp only [fV]) <;> nums
    obtain e₂ : tailOf P L u'.mem = tailOf P L t.mem := tail_frame hW fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact tail_w hL r hr
      · simp only [List.mem_singleton] at hr; subst hr
        refine Offset.disjoint _ (.inl ?_) ?_ ?_ <;> nums
    rw [e₁, e₂]

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.seq (WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, hSu⟩ => ?_)
  refine WP.mono (vfin_ok hL hT hu (dst := fV) (by simp only [fV]; omega_using [])) fun t' ⟨hc', hf', hm⟩ => ?_
  obtain hR : Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, 128⟩ ⟨L.scr + BitVec.ofNat 64 0, 8 * 48⟩ :=
    hL.stk_scr (by omega_using []) (by decide)
  obtain hk : kOf P L t'.mem = kOf P L t.mem := by
    show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 128) P.v.H.D = _
    rw [kv_frame hL hf' (o := 128) (by decide) (.inl (by simp only [fV]; nums)) (by nums) (by simp only [fV]; nums)]
    exact bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  obtain hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hR.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
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
        (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) ∧
      tailOf P L t'.mem = tailOf P L t.mem := by
  have hnB := hL.nB
  obtain post : ∀ {u : State}, St P L g lr m₀ (Spec.Hmac.blockKey P.v.ok.SH.H (kOf P L t.mem)) [] u →
      ∀ {ws : List Region}, Frame ws t.mem u.mem → (∀ r ∈ ws, ∃ r' ∈ KVW L, Region.Sub r r') →
      (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 192, P.v.H.D⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 2256, len⟩ r) →
      (∀ r ∈ ws, Region.Disjoint ⟨L.scr + BitVec.ofNat 64 (2256 + 1), 2 * P.Q⟩ r) →
      WP isa (.seq (cfgOf P).updV (.seq ((cfgOf P).updM len) ((cfgOf P).fin len fK))) u fun t' =>
        Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem)
          (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) ∧
        tailOf P L t'.mem = tailOf P L t.mem := by
    intro u hu ws hf hk hdv hdm hdt
    refine WP.mono (vmfin_ok hL hT hu hlen) fun t' ⟨hc', hf', hm⟩ => ⟨hc', ?_, ?_, ?_, ?_⟩
    · exact (hf.sub hk).trans (hf'.sub (wd_kvw (P := P) (dst := fK) (by simp only [fK]; nums)))
    · show Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 192) P.v.H.D = _
      rw [kv_frame hL hf' (o := 192) (by decide) (.inr (by simp only [fK]; nums)) (by nums) (by simp only [fK]; nums)]
      exact bytesAt_frame hf hdv (by nums)
    · rw [hm]
      obtain hv : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hf hdv (by nums)
      obtain hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) len =
          Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len := bytesAt_frame hf hdm (by omega_using [hlen])
      rw [hv, hmsg, mac_eq]
    · have e₁ : tailOf P L t'.mem = tailOf P L u.mem := tail_frame hf' fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact tail_w hL r hr
        · simp only [List.mem_singleton] at hr; subst hr
          refine (hL.stk_scr ?_ ?_).symm <;> (try simp only [fK]) <;> nums
      rw [e₁, tail_frame hf hdt]
  cases fresh
  · refine WP.seq (WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, hfu, _⟩ => ?_)
    have hu' : St P L g lr m₀ (Spec.Hmac.blockKey P.v.ok.SH.H (kOf P L t.mem)) [] u := hu
    refine post hu' hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
    · exact hL.stk_scr (by nums) (by decide)
    · exact Offset.disjoint _ (by omega_using []) (by omega_using [hlen]) (by decide)
    · exact Offset.disjoint _ (.inr (by decide)) (by nums) (by decide)
  · refine WP.seq (WP.mono (init_step hL hT hc) fun u ⟨hu, hfu⟩ => ?_)
    refine post hu hfu (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) (tail_w hL) <;>
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨L.B, 256⟩, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact hL.stk_scr0 (by nums) (by decide)
    · exact Offset.disjoint_base _ (by omega_using []) (by nums)
    · exact Offset.disjoint_base _ (by decide) (by omega_using [hlen])
    · exact hL.low_scr (by omega_using [hlen]) |>.symm

/-- What the steps need of the layout: the scalars' bytes, and the table of `P`. -/
def HOk (P : RfcHash) (L : Lay dn) : Prop := L.q = P.Q ∧ TabL P L ∧ L.cs = P.R.C.cs

/-- `K = HMAC_K(V ‖ m)`, then `V = HMAC_K(V)`, for the message `m = b (‖ d ‖ h)`
(of `mlen P full` bytes), `d ‖ h` written if `wr`, and kept since if not. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) {b : Nat} (hb : b < 2 ^ 15)
    (wr full : Bool) (fresh : Bool) (hS : fresh = false → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block ((cfgOf P).msg b wr))
      (.seq ((cfgOf P).hmacK fresh (mlen P full)) (cfgOf P).hmacVS))) t
      fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then (if wr then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else tailOf P L t.mem)
            else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) ∧
        tailOf P L t'.mem = (if wr then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else tailOf P L t.mem) := by
  have hT := hq.2.1
  refine WP.seq (WP.mono (msgPtrs_ok hL hc) fun p ⟨hcp, hmp, _, h11, h9, h10⟩ => ?_)
  rw [← hmp] at hS ⊢
  refine WP.seq (WP.mono (msg_ok (P := P) hL hq.1 hcp h11 h9 h10 hb wr) fun u ⟨hcu, hfu, hbu, htu⟩ => ?_)
  obtain hsafe : Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, 128⟩ ⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ :=
    hL.stk_scr (by omega_using []) (by nums)
  obtain hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  obtain hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hsafe.sub_left (Offset.sub _ (by omega_using []) (by nums))) (by nums)
  obtain hSu : fresh = false → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸
    (hS h).frame (blockKey_length (keyOf_length _)) hfu fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by nums) (by nums) (by nums)
  obtain hmsg : Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (mlen P full) =
      [BitVec.ofNat 8 b] ++ (if full then tailOf P L u.mem else []) := by
    cases full
    · exact hbu
    · show Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) (1 + 2 * P.Q) = _
      rw [Proof.Hmac.Common.bytesAt_add, Offset.add_add, hbu]; rfl
  refine WP.seq (WP.mono (hmacKB_ok (P := P) hL hT hcu (len := mlen P full)
    (by cases full <;> simp only [mlen, Bool.false_eq_true, ite_true, ite_false] <;> nums) fresh hSu)
    fun w ⟨hcw, hfw, hvw, hkw, htw⟩ => ?_)
  refine WP.mono (hmacVS_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv', hs', ht'⟩ => ⟨hc', ?_, ?_, ?_, hs', ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by nums)))).trans hfw).trans hf'
  · rw [hk', hkw, hku, hvu, hmsg, htu, List.append_assoc]
  · rw [hv', hk', hvw, hvu]
  · rw [ht', htw, htu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g): for
`b ≠ 0`, `d ‖ h` already follows the message's first byte. -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) (b : Nat) (hb : b < 2 ^ 15)
    (hS : b ≠ 0 → SavedK P L t.mem (kOf P L t.mem))
    (ht : b ≠ 0 → tailOf P L t.mem = Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) ∧
      tailOf P L t'.mem = Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem := by
  unfold Cfg.rekeyFull
  refine WP.mono (rekey_gen hL hq hc hb (decide (b = 0)) true (decide (b = 0)) fun h => hS (by simpa using h))
    fun t' h => ?_
  rcases Nat.eq_zero_or_pos b with rfl | hpos
  · simpa using h
  · have hb0 : b ≠ 0 := by omega_using [hpos]
    obtain e : decide (b = 0) = false := by simp [hb0]
    rw [e] at h
    simp only [ite_true, Bool.false_eq_true, ite_false] at h
    rw [ht hb0] at h
    exact h

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g lr m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) :=
  WP.mono (rekey_gen (b := 0) hL hq hc (by decide) false false true (fun h => absurd h (by decide)))
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2.1, h.2.2.2.2.1⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

end

end


/-!
# Deterministic ECDSA on PPC64LE: the candidate

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Cand.lean`): the candidate `T`,
at `fT` above the frame's pointers, its length at `fTlen`: empty
(`tInit_ok`), then, while it is shorter than `Q` bytes, `V = HMAC_K(V)`
appended to it (`step_ok`: `hmacVR_ok`, `keepArgs_ok`, `cp_ok`, `tStep_ok`,
whose `r12` is the borrow of `|T| - Q` as a mask), which the loop does
`nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks (`nV_eq`): `T` is then
`genT`'s (`loop_ok`), and `k`, its first `Q` bytes, shifted right by `sh`
bits if `big` (`candTop_ok`), is `bits2int` of it (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 (96 + fTlen)) 64

/-- `T`'s first `n` bytes. -/
abbrev tOf (L : Lay dn) (m : Mem) (n : Nat) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (96 + fT)) n

/-- Where `core` reads `k`: `T`. -/
abbrev kArg (_P : RfcHash) (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (96 + fT)

/-! ## The blocks -/

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g lr m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] t.mem t'.mem ∧ tlen L t'.mem = BitVec.ofNat 64 0 := by
  refine WP.of_syms (stepLi (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  refine stepAddSp (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide)
    (by rw [v₂, k₁.sp, hc.sp, BitVec.add_zero, fr_add])
    (by rw [k₂.wr, k₁.wr]; exact hc.inFrW (by decide) (by decide)) fun t₃ k₃ g₃ m₃ => wp_nil fun hsy => ?_
  obtain K : Kp [.r9, .r11] t t₃ := (k₁.mono.trans k₂.mono).trans k₃.mono
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] t.mem t₃.mem := by
    rw [m₃, m₂, m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by decide)) hsy, hf, ?_⟩
  show Mem.readW _ _ 64 = _
  rw [m₃, Mem.readW_writeW_self64, k₂.gpr _ (by decide), v₁]

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`r4`, `T + a` in `r5`, `r6 = D`. -/
theorem keepArgs_ok (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 64 a) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Kp [.r4, .r5, .r6, .r9, .r11] t u → u.mem = t.mem → u.gpr .r4 = L.B + BitVec.ofNat 64 (96 + fV) →
      u.gpr .r5 = L.B + BitVec.ofNat 64 (96 + fT + a) → u.gpr .r6 = BitVec.ofNat 64 P.v.H.D →
      WP isa (.block is) u Q) :
    WP isa (.block (Cfg.keepArgs ++ is)) t Q := by
  simp only [Cfg.keepArgs, List.cons_append, List.nil_append]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  obtain hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepAddSp (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepAddSp (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add])
    (by rw [k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hc.inFr (by decide) (by decide))
    fun t₄ k₄ m₄ v₄ => ?_
  refine stepAdd fun t₅ k₅ m₅ v₅ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add]; rfl)
    (by rw [k₅.rd, k₅.wr, k₄.rd, k₄.wr, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hc.inFr (by omega_using []) (by omega_using []))
    fun t₆ k₆ m₆ v₆ => ?_
  obtain hm : t₆.mem = t.mem := by rw [m₆, m₅, m₄, m₃, m₂, m₁]
  refine k t₆ (((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono) hm ?_ ?_ ?_
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, k₁.sp, hc.sp,
      fr_add]
  · rw [k₆.gpr _ (by decide), v₅, k₄.gpr _ (by decide), v₃, v₄, m₃, m₂, m₁,
      show t.mem.readW (L.B + BitVec.ofNat 64 (96 + fTlen)) 64 = tlen L t.mem from rfl, ha, k₂.sp, k₁.sp, hc.sp,
      fr_add, Offset.add_add, Nat.add_assoc]
  · rw [v₆, m₅, m₄, m₃, m₂, m₁, hc.dl hT]

/-- `|T| < Q` from the borrow of `|T| - Q`, as a mask. -/
theorem mask_lt {a q : Nat} (_ha : a < 2 ^ 63) (hq : q < 2 ^ 63) :
    (BitVec.ofNat 64 ((a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
      (decide (2 ^ 64 ≤ a + (2 ^ 64 - 1 - q) + 1)).toNat) != 0) = decide (a < q) := by
  by_cases h : q ≤ a
  · rw [decide_eq_true (by omega : 2 ^ 64 ≤ a + (2 ^ 64 - 1 - q) + 1), decide_eq_false (by omega_using [h] : ¬ a < q),
      show (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
        (true).toNat = 2 ^ 64 by simp only [Bool.toNat_true]; omega_using []]
    rfl
  · rw [decide_eq_false (by omega_using [_ha, h] : ¬ 2 ^ 64 ≤ a + (2 ^ 64 - 1 - q) + 1), decide_eq_true (by omega_using [h] : a < q),
      show (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64 + (2 ^ 64 - 1 - (a + (2 ^ 64 - 1 - q) + 1) % 2 ^ 64) +
        (false).toNat = 2 ^ 64 - 1 by simp only [Bool.toNat_false]; omega_using []]
    rfl

/-- `T` longer by `D` bytes, and `r12 ≠ 0` iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g lr m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 64 a) (hn : a + P.v.H.D < 2 ^ 63) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g lr m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 64 (a + P.v.H.D) ∧
      isa.eval (.nonzero .d .r12) u' = some (decide (a + P.v.H.D < P.Q)) := by
  have hs := P.sizes
  simp only [Cfg.tStep]
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  obtain hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide) (by rw [hb, fr_add])
    (hc.inFrK k₁ (by decide) (by decide)) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl)
    (by rw [k₂.rd, k₂.wr]; exact hc.inFrK k₁ (by omega_using []) (by omega_using [])) fun t₃ k₃ m₃ v₃ => ?_
  refine stepAdd fun t₄ k₄ m₄ v₄ => ?_
  obtain e9 : t₄.gpr .r9 = BitVec.ofNat 64 (a + P.v.H.D) := by
    rw [v₄, k₃.gpr _ (by decide), v₂, v₃, m₂, m₁, show u.mem.readW (L.B + BitVec.ofNat 64 (96 + fTlen)) 64 =
      tlen L u.mem from rfl, ha, hc.dl hT, BitVec.ofNat_add_ofNat]
  refine stepStd (a := L.B + BitVec.ofNat 64 (96 + fTlen)) (by decide) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb, fr_add])
    (by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]; exact hc.inFrW (by decide) (by decide)) fun t₅ k₅ g₅ m₅ => ?_
  refine stepLi (show (cfgOf P).len < 2 ^ 15 by show P.Q < _; omega_using [hs]) fun t₆ k₆ m₆ v₆ => ?_
  refine stepSubc fun t₇ k₇ m₇ v₇ c₇ => ?_
  refine stepSube fun t₈ k₈ m₈ v₈ => wp_nil fun hsy => ?_
  obtain K : Kp [.r9, .r10, .r11, .r12] u t₈ :=
    ((((((k₁.mono.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono).trans k₇.mono).trans
      k₈.mono
  obtain hm : t₈.mem = t₄.mem.writeW (L.B + BitVec.ofNat 64 (96 + fTlen)) (t₄.gpr .r9) := by
    rw [m₈, m₇, m₆, m₅]
  obtain hm₄ : t₄.mem = u.mem := by rw [m₄, m₃, m₂, m₁]
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 (96 + fTlen), 8⟩] u.mem t₈.mem := by
    rw [hm, hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
      intro h; simp at h; rcases h with rfl | rfl | rfl | rfl <;> simp [preserved] at hr)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by decide)) hsy, hf,
    by show Mem.readW _ _ 64 = _; rw [hm, Mem.readW_writeW_self64, e9], ?_⟩
  obtain e9' : (t₆.gpr .r9).toNat = a + P.v.H.D := by
    rw [k₆.gpr _ (by decide), g₅, e9, BitVec.toNat_ofNat]; omega_using [hn]
  obtain e10 : (t₆.gpr .r10).toNat = P.Q := by rw [v₆, BitVec.toNat_ofNat]; show P.Q % _ = _; omega_using [hs]
  refine (eval_nonzero t₈ .r12).trans ?_
  rw [v₈, v₇, c₇, e9', e10, BitVec.toNat_ofNat]
  exact congrArg some (mask_lt (a := a + P.v.H.D) (q := P.Q) (by omega_using [hn]) (by omega_using [hs]))

/-! ## The loop -/

/-- `genT` with one more `V`: the last after the others. -/
theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (k + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K k V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    show (Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K (k + 1) (Spec.Hmac.hmac H K V)).2) =
      ((Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).1) ++
          Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K k (Spec.Hmac.hmac H K V)).2)
    rw [genT_succ H K k (Spec.Hmac.hmac H K V)]
    simp

theorem genT_length (P : RfcHash) (K : List Byte) : ∀ (k : Nat) (V : List Byte),
    (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H K k V).1.length = k * P.v.H.D
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | k + 1, V => by
    rw [genT_succ, List.length_append, genT_length P K k V, mac_length]
    rw [Nat.succ_mul]

/-- What the candidate's loop changes: `scratch`, the stack below the
frame's pointers, and `T`. -/
abbrev CW (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 264⟩, ⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 64 (j * P.v.H.D)
  t : tOf L u.mem (j * P.v.H.D) = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H K j V₀).1
  saved : SavedK P L u.mem K

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat}
    (hj : (j + 1) * P.v.H.D ≤ 136) {u : State} (hI : CI P L g lr m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g lr m₀ t₀ K V₀ (j + 1) u' ∧
      isa.eval (.nonzero .d .r12) u' = some (decide ((j + 1) * P.v.H.D < P.Q)) := by
  have hnB := hL.nB
  have hs := P.sizes
  obtain hjD : (j + 1) * P.v.H.D = j * P.v.H.D + P.v.H.D := Nat.succ_mul _ _
  obtain hS : SavedK P L u.mem (kOf P L u.mem) := by rw [hI.k]; exact hI.saved
  obtain hkl := blockKey_length (P := P) (keyOf_length (L := L) u.mem)
  refine WP.seq (WP.mono (hmacVR_ok hL hT hI.ctx hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hS₁⟩ => ?_)
  obtain hl₁ : tlen L u₁.mem = BitVec.ofNat 64 (j * P.v.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega_using [])
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega_using []) (by simp only [fTlen]; omega_using [])) (by decide)
  obtain ht₁ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (96 + fT)) (j * P.v.H.D) =
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fT)) (j * P.v.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fT]; omega_using [hj, hjD])
      · exact Offset.disjoint_base _ (by simp only [fT]; omega_using []) (by simp only [fT]; omega_using [hj, hjD])) (by omega_using [hj, hjD])
  refine WP.seq (WP.of_syms ?_)
  rw [← List.append_nil Cfg.keepArgs]
  refine keepArgs_ok (is := []) hT hc₁ hl₁ fun u₂ k₂ m₂ h4 h5 h6 => wp_nil fun hsy₂ => ?_
  obtain hc₂ : Ctx L g lr m₀ u₂ := hc₁.kp hL k₂ m₂ hsy₂
  refine WP.seq (WP.mono (cp_ok hL hc₂ (p := L.B + BitVec.ofNat 64 (96 + fT + j * P.v.H.D))
      (q := L.B + BitVec.ofNat 64 (96 + fV)) (n := P.v.H.D) (by omega_using [hs]) (by omega_using [hs]) h4 h5 h6
      (fun i hi => by rw [Offset.add_add]; exact hc₂.inFrW (n := 1) (by simp only [fT]; omega_using []) (by simp only [fT]; omega_using [hj, hjD, hi]))
      (safe_high L (by simp only [fT]; omega_using []) (by simp only [fT]; omega_using [hj, hjD]))
      (fun i hi => by rw [Offset.add_add]; exact hc₂.inFr (n := 1) (by simp only [fV]; omega_using []) (by simp only [fV]; omega_using [hs, hi]))
      (Offset.disjoint _ (.inl (by simp only [fV, fT]; omega_using [hs])) (by simp only [fV]; omega_using [hs]) (by simp only [fT]; omega_using [hj, hjD]))
      (by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by simp only [fT]; omega_using [hj, hnB, hjD]),
          Nat.mod_eq_of_lt (by simp only [fT]; omega_using [hj, hjD])]; simp only [fT]; omega_using [hj, hnB, hjD]))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_)
  rw [m₂] at hf₃ hb₃
  obtain hl₃ : tlen L u₃.mem = BitVec.ofNat 64 (j * P.v.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega_using [])) (by simp only [fTlen]; omega_using [])
        (by simp only [fT]; omega_using [hj, hjD])) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega_using [hj, hjD])) fun u₄ ⟨hc₄, hf₄, hl₄, hcf₄⟩ => ?_
  -- What the copy and the length's store keep.
  obtain kp : ∀ {o n : Nat}, 96 ≤ o → o + n ≤ 96 + fTlen →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) n :=
    fun h₁ h₂ => by
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl h₂) (by simp only [fTlen] at h₂ ⊢; omega_using [h₂]) (by simp only [fTlen]; omega_using []))
        (by simp only [fTlen] at h₂; omega_using [h₂]),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by simp only [fTlen, fT] at h₂ ⊢; omega_using [h₂])) (by simp only [fTlen] at h₂ ⊢; omega_using [h₂])
            (by simp only [fT]; omega_using [hj, hjD])) (by simp only [fTlen] at h₂; omega_using [h₂])]
  obtain hK : kOf P L u₄.mem = K := by
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 128) P.v.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega_using [hs])]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, ?_⟩, by rw [hcf₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 264⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩, by simp, Offset.sub _ (by omega_using []) (by omega_using [hj, hjD])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 264⟩, by simp, Offset.sub_base _ (by simp only [fTlen]; omega_using [])⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 192) P.v.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega_using [hs]), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (96 + fT)) ((j + 1) * P.v.H.D) = _
    rw [hjD, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega_using [])) (by simp only [fT]; omega_using [hj, hjD])
          (by simp only [fTlen]; omega_using [])) (by omega_using [hj, hjD]),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega_using [])) (by simp only [fT]; omega_using [hj, hjD])
          (by simp only [fTlen]; omega_using [])) (by omega_using [hs]),
      hb₃, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [])) (by simp only [fT]; omega_using [hj, hjD]) (by simp only [fT]; omega_using [hj, hjD])) (by omega_using [hj, hjD]),
      ht₁, show Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fT)) (j * P.v.H.D) = _ from hI.t, genT_succ]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (96 + fV)) P.v.H.D = vOf P L u₁.mem from rfl, hv₁,
      hI.k, hI.v]
  · rw [hk₁, hI.k] at hS₁
    refine (hS₁.frame (by rw [← hI.k]; exact hkl) hf₃ fun r hr => ?_).frame (by rw [← hI.k]; exact hkl)
      hf₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fT]; omega_using [hj, hjD]) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fTlen]; omega_using []) (by decide)).symm

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.v.H.D - 1) / P.v.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.v.H.D < P.Q := by
  have hs := P.sizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega_using [hs]), Nat.succ_mul (j + 1)]
  omega_using [hs]

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.v.H.D ≤ P.Q + P.v.H.D - 1 ∧ P.Q ≤ P.nV * P.v.H.D := by
  have hs := P.sizes
  obtain e₁ := Nat.div_mul_le_self (P.Q + P.v.H.D - 1) P.v.H.D
  obtain e₂ := Nat.lt_mul_div_succ (P.Q + P.v.H.D - 1) (show 0 < P.v.H.D by omega_using [hs])
  obtain e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega_using [hs])).mpr (by omega_using [hs])
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.v.H.D - 1) / P.v.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega_using [e₁, e₂, e₃]

/-- `nBits` is within the scalars' last byte. -/
theorem nBits_len (P : RfcHash) : 8 * P.Q < Spec.Ecdsa.nBits P.R.C.E.curve + 8 ∧
    Spec.Ecdsa.nBits P.R.C.E.curve ≤ 8 * P.Q := by
  cases h : P.R.big
  · have := (P.R.sizesA h).2.2.1; simp only [RfcHash.Q, RfcCurve.Q] at this ⊢; omega_using [this]
  · have := P.R.sizesW h; simp only [RfcHash.Q, RfcCurve.Q] at this ⊢; omega_using [this]

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.C.E.curve P.v.H.D = P.nV := by
  have hs := P.sizes
  obtain hl := nBits_len P
  obtain e₁ := Nat.div_mul_le_self (P.Q + P.v.H.D - 1) P.v.H.D
  obtain e₂ := Nat.lt_mul_div_succ (P.Q + P.v.H.D - 1) (show 0 < P.v.H.D by omega_using [hs])
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV] at e₁ e₂ ⊢
  generalize (P.Q + P.v.H.D - 1) / P.v.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  obtain h₁ : N * (8 * P.v.H.D) = 8 * (N * P.v.H.D) := Nat.mul_left_comm _ _ _
  obtain h₂ : (N + 1) * (8 * P.v.H.D) = 8 * (N * P.v.H.D) + 8 * P.v.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega_using [hl, e₁, h₁]) (by omega_using [hl, e₂, h₂])

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g lr m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep (.nonzero .d .r12)) u (CI P L g lr m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  have hs := P.sizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g lr m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  obtain hb : (j + 1) * P.v.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega_using [hj]) (Nat.le_refl P.v.H.D)) (by omega_using [hND, hs])
  refine WP.mono (step_ok hL hT hb hIj) fun s' ⟨hI', hcf⟩ => ?_
  by_cases hlt : j + 1 < P.nV
  · exact .inr ⟨by rw [hcf, decide_eq_true ((nV_lt P j).mp hlt)], P.nV - (j + 1), by omega_using [hj], j + 1, rfl, hlt, hI'⟩
  · refine .inl ⟨by rw [hcf, decide_eq_false (fun h => hlt ((nV_lt P j).mpr h))], ?_⟩
    rw [show P.nV = j + 1 by omega_using [hj, hlt]]; exact hI'

/-! ## The candidate -/

/-- `T` empty: no `V`s yet. -/
theorem tInit_ci (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.block Cfg.tInit) t (CI P L g lr m₀ t (kOf P L t.mem) (vOf P L t.mem) 0) := by
  have hs := P.sizes
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀⟩ => ?_
  obtain kv0 : ∀ {o : Nat}, 96 ≤ o → o + P.v.H.D ≤ 256 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.v.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.v.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen]; omega_using [h₂])) (by omega_using [h₂]) (by simp only [fTlen]; omega_using []))
      (by omega_using [hs])
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B, 264⟩, by simp, Offset.sub_base _ (by decide)⟩
      k := kv0 (by decide) (by omega_using [hs])
      v := kv0 (by decide) (by omega_using [hs])
      len := by rw [hl₀, Nat.zero_mul]
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      saved := hS.frame (blockKey_length (keyOf_length _)) hf₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by simp only [fTlen]; omega_using []) (by decide)).symm }

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- If `big`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_ok (hL : L.Ok) (hW : P.R.big = true) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block (cfgOf P).candTop) t fun u => Ctx L g lr m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2560, 72⟩, ⟨L.B + BitVec.ofNat 64 (96 + fT), 66⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fT)) 66 =
        Spec.Weierstrass.toBytes 66
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (96 + fT)) 66) >>> P.R.sh) := by
  obtain ⟨hw9, hQ66, -⟩ := P.sizesW hW
  obtain hsh := P.R.sh7 hW
  have hsc : (cfgOf P).sh = P.R.sh := rfl
  have hbc : (cfgOf P).big = true := hW
  rw [Cfg.candTop, hbc, ite_eq_left_of_eq_true _ _ (eq_self true), hsc]
  exact WP.mono (conv_ok hL (c := cfgOf P) (o := fT) (s := P.R.sh) hQ66 hw9 hc (by decide) (by decide) (by omega_using [hsh])
    (by omega_using [hsh])) fun u ⟨hcu, _, hf, hb⟩ => ⟨hcu, hf, hb⟩

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).cand t fun u => Ctx L g lr m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve
          (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L t.mem) := by
  have hs := P.sizes
  obtain hl := nBits_len P
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci hL hc hS) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  obtain hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  obtain hsh : 8 * P.Q - Spec.Ecdsa.nBits P.R.C.E.curve = P.R.sh := by rw [P.R.sh_eq]
  obtain hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.C.E.curve
      (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kArg P L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, Rfc6979.hashToInt_takeR (R := P.Q) hl.2 (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.v.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kArg P L) (P.nV * P.v.H.D) from hI₁.t.symm,
      bytesAt_take _ _ hQN, hsh]
  cases hb : P.R.big
  · have hsh0 : P.R.sh = 0 := P.R.sh0 hb
    rw [show (cfgOf P).candTop = [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh0, Nat.shiftRight_zero], hI₁.saved⟩
  · have hQ66 : P.Q = 66 := (P.sizesW hb).2.1
    refine WP.mono (candTop_ok hL hb hI₁.ctx) fun u ⟨hcu, hf, hbu⟩ => ?_
    obtain kv : ∀ {o : Nat}, 96 ≤ o → o + P.v.H.D ≤ 256 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.v.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.v.H.D := fun h₁ h₂ =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega_using [h₂]) (by decide)
        · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_using [h₂])) (by omega_using [h₂]) (by simp only [fT]; omega_using [])) (by omega_using [hs])
    refine ⟨hcu, hI₁.frame.trans (hf.sub fun r hr => ?_), (kv (by decide) (by omega_using [hs])).trans hI₁.k,
      (kv (by decide) (by omega_using [hs])).trans hI₁.v, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 (96 + fT), 136⟩, by simp, Region.sub_prefix (by omega_using [])⟩
    · rw [show kArg P L = L.B + BitVec.ofNat 64 (96 + fT) from rfl, hQ66, hbu, hbits, hQ66,
        Rfc6979.ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := Rfc6979.ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (96 + fT)) 66)
          rwa [length_bytesAt] at this))]
    · refine hI₁.saved.frame (blockKey_length (keyOf_length (L := L) t.mem)) hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (hL.stk_scr (by simp only [fT]; omega_using []) (by decide)).symm

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
