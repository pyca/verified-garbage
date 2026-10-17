module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Wide
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: `h` and `core`'s digest

From the digest of `D` bytes (`digest`, in `rsi`), into the frame
(`prep_ok`): `core`'s digest `Y` (and, for P-521, `h`) cleared
(`prepZero_ok`); the case of the hash function of a dispatch, which copies
the digest into them (`prepCase_ok`): unless `wide`, its `min D Q` leftmost
bytes to the end of `Y`'s `Q`, which makes `X`, the `Q`-byte number
`bits2int` takes of the digest; if `wide`, the digest after `Q - D - 1` zero
bytes in `Y` (then one more), and after `Q - D` in `h`. Then, unless `wide`,
`h` is `X` modulo `n` (`reduce_ok`), and `core`'s digest is `X`; if `wide`,
`Y` shifted right by `8 - sh` bits is the digest's number shifted left by
`sh`, and `h` is the digest after `Q - D` zero bytes, RFC 6979's
`bits2octets` (`prepPost_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The words cleared, from `Y`. -/
abbrev nz (P : RfcHash) : Nat := if P.R.wide then 18 else 9

theorem zeroY_ok {t : State} (hc : Ctx L g m₀ t) : ∀ k ≤ 18, ∀ u : State,
    u.wr = t.wr → u.gpr .rsp = t.gpr .rsp → u.gpr .rcx = 0 →
    WP isa (.block ((List.range k).map fun j => .store (stk (fY + 8 * j)) .rcx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 240, 8 * k⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 240 + BitVec.ofNat 64 (8 * j)) 64 = 0
  | 0, _, u, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk, u, hwu, hsu, hcx => by
    have he := L.he
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroY_ok hc k (by omega) u hwu hsu hcx) fun u₁ ⟨hrd, hwr, hg, hf, hz⟩ => ?_
    have w := hc.inFrW (d := 240 + 8 * k) (n := 8) (by omega) (by omega)
    rw [← hwu, ← hwr] at w
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hg, hsu, hcx, hc.rsp, fY,
      Offset.add_add, show 24 + (216 + 8 * k) = 240 + 8 * k by omega, w, ite_true, Option.some.injEq,
      exists_eq_left']
    have hw : Frame [⟨L.B + BitVec.ofNat 64 (240 + 8 * k), 8⟩] u₁.mem
        (u₁.mem.writeW (L.B + BitVec.ofNat 64 (240 + 8 * k)) (0 : BitVec 64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hf' : Frame [⟨L.B + BitVec.ofNat 64 240, 8 * (k + 1)⟩] u.mem
        (u₁.mem.writeW (L.B + BitVec.ofNat 64 (240 + 8 * k)) (0 : BitVec 64)) :=
      (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩).trans
      (hw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)
    refine ⟨hrd, hwr, trivial, hf', fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have := hz j hj
      rw [Offset.add_add] at this
      rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact this
    · exact Mem.readW_writeW_self64 _ _ _

theorem zeros_bytes (n : Nat) :
    (List.range n).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) = List.replicate n 0 := by
  rw [show (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) = fun _ => (0 : BitVec 8) from
    funext fun i => by simp, List.map_const', List.length_range]

/-- `Y` (and, if `wide`, `h`) cleared, and `hash` in `rax`. -/
theorem prepZero_ok (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).prepZero) t fun t' => Ctx L g m₀ t' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t'.gpr r = t.gpr r) ∧ t'.gpr .rax = BitVec.ofNat 64 P.k ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 8 * nz P⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) (8 * nz P) = List.replicate (8 * nz P) 0 := by
  have hnz : nz P ≤ 18 := by simp only [nz]; split <;> omega
  rw [Cfg.prepZero, WP.block_append_iff, WP.block_append_iff]
  have h₁ : WP isa (.block [.alu32 .xor .rcx (.reg .rcx)]) t fun u => Ctx L g m₀ u ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ u.mem = t.mem ∧ u.gpr .rcx = 0 ∧ ∀ r, r ≠ .rcx → u.gpr r = t.gpr r := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
      Option.some.injEq, exists_eq_left', xor_self_zx]
    exact ⟨hc.regs hL rfl rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv, fun r hr => by simp [hr]⟩
  have e : (if (cfgOf P).wide then 18 else 9) = nz P := rfl
  rw [e]
  refine WP.mono h₁ fun u ⟨hcu, hrd, hwr, hm, hcx, hg⟩ => ?_
  refine WP.mono_syms (zeroY_ok hcu (nz P) hnz u rfl rfl hcx) fun u' ⟨hrd', hwr', hg', hf', hz'⟩ hsy => ?_
  have hc' : Ctx L g m₀ u' := hcu.keep hL hrd' hwr' (by rw [hg']) (fun r _ _ => by rw [hg']) hf'
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact safe_high L (by omega) (by simp only [nz]; split <;> omega)) hsy
  refine WP.mono (ldSel_ok hL hq hc') fun t' h => ⟨h.ctx, fun r h₁ h₂ => ?_, h.val, ?_, ?_⟩
  · rw [h.keep r h₁, hg', hg r h₂]
  · rw [h.mem, ← hm]; exact hf'
  · rw [h.mem, bytesAt_of_readW _ _ 0 hz', zeros_bytes]

/-- The `n` bytes at `[src + so]` to `[rsp + d]`, above the frame's pointers,
by `copyBytes`, with `Ctx` kept. -/
theorem copyBF_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) {so d n : Nat} (h8 : 8 ≤ n) (hd₁ : 216 ≤ d) (hd₂ : 24 + d + n ≤ 520) (hso : so + n < 2 ^ 64)
    (hr : ∀ j, j + 8 ≤ n → InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, n⟩ ⟨L.B + BitVec.ofNat 64 (24 + d), n⟩) :
    WP isa (.block (Cfg.copyBytes n src so .rsp d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + d), n⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (24 + d)) n =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) n := by
  have he := L.he
  refine WP.mono_syms (copyBytes_ok (D := L.B + BitVec.ofNat 64 24) (d := d) (by decide) hsr (by rw [fr_add]; exact hsep)
    h8 hso (by omega) hs hc.rsp hr fun j hj => by
      rw [fr_add, show 24 + (d + j) = (24 + d) + j by omega]; exact hc.inFrW (by omega) (by omega))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy => ?_
  rw [fr_add] at hf hb
  exact ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) hd₂) hsy, hg, hf, hb⟩

/-- `X`, the `Q`-byte number `bits2int` takes of a digest `dg`, for a curve
whose `nBits` is `8 Q`: its leftmost `Q` bytes, or it after `Q - D` zero
bytes if it is shorter. -/
def xOfDg (Q : Nat) (dg : List Byte) : List Byte :=
  List.replicate (Q - min dg.length Q) 0 ++ dg.take Q

/-- A dispatch on the hash function: the case of `P`'s, from a state of other flags. -/
theorem dispatch_ok (P : RfcHash) {f : Impl.Pbkdf2.Md.X86_64.Hash → Prog isa} {s : State}
    {Q : State → Prop} (hs : s.gpr .rax = BitVec.ofNat 64 P.k)
    (h : ∀ s', Proof.Dispatch.X86_64.FlagsOnly s s' → WP isa (f P.H) s' Q) :
    WP isa (Impl.Dispatch.X86_64.chain ((cfgOf P).hs.map fun p => (p.1, f p.2))) s Q := by
  have hk := P.hk
  have hk8 : P.k < 8 := by
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hsel : Proof.Dispatch.X86_64.sel s = P.k := by
    rw [Proof.Dispatch.X86_64.sel, hs, BitVec.toNat_ofNat]; omega
  have hkeys := keys_cases P f
  refine Proof.Dispatch.chain_wp Proof.Dispatch.X86_64.tests _ ?_ ?_ ?_ fun c hc s' hr _ => ?_
  · intro i hi
    rw [Proof.Dispatch.keys, hkeys] at hi
    simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  · rw [Proof.Dispatch.keys, hkeys, hsel]; exact hk
  · rw [Proof.Dispatch.keys, hkeys]; decide
  · rw [hsel] at hc
    rw [case_eq P f hc]
    exact h s' hr

/-- Bytes within a run of zero bytes. -/
theorem zeros_sub {m : Mem} {p : Addr} {N : Nat} (hz : Spec.Sha256.bytesAt m p N = List.replicate N 0) {a n : Nat}
    (h : a + n ≤ N) : Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 a) n = List.replicate n 0 := by
  have e := bytesAt_take m p h
  rw [hz, List.take_replicate, Nat.min_eq_left h, Proof.Hmac.Common.bytesAt_add, ← List.replicate_append_replicate] at e
  exact (List.append_inj e (by simp [Spec.Sha256.bytesAt])).2

/-- The digest's copies, unless `wide`: `Y`'s `Q` bytes are `X`. -/
theorem prepCaseA_ok (hL : L.Ok) (hA : P.R.wide = false) {t : State} (hc : Ctx L g m₀ t) (hdn : P.H.D ≤ dn)
    (hsi : t.gpr .rsi = L.dg) (hz : Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 240) 72 = List.replicate 72 0) :
    WP isa (.block ((cfgOf P).prepCase P.H.D)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 72⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        xOfDg P.Q (Spec.Sha256.bytesAt t.mem L.dg P.H.D) := by
  obtain ⟨hQ8, h8, hQ64⟩ := P.sizesA hA
  have hD := P.sizes
  have he := L.he
  have hm : 8 ≤ min P.H.D P.Q := by nums
  have hl : (Spec.Sha256.bytesAt t.mem L.dg P.H.D).length = P.H.D := by simp [Spec.Sha256.bytesAt]
  have e : (cfgOf P).prepCase P.H.D = Cfg.copyBytes (min P.H.D P.Q) .rsi 0 .rsp (fY + (P.Q - min P.H.D P.Q)) := by
    simp only [Cfg.prepCase, cfgOf, hA, Bool.false_eq_true, ite_false]
  rw [e]
  refine WP.mono (copyBF_ok hL hc (S := L.dg) hsi (by decide) (so := 0) hm (by simp only [fY]; omega)
    (by simp only [fY]; nums) (by nums)
    (fun j hj => by rw [Nat.zero_add]; exact hc.inDg (by nums) (by nums))
    (by rw [add_ofNat_zero]
        exact (hL.stk_DG (by simp only [fY]; nums)).symm.sub_left (Region.sub_prefix (by nums))))
    fun u ⟨hcu, _, hf, hb⟩ => ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by simp only [fY]; omega) (by simp only [fY]; nums)⟩, ?_⟩
  simp only [fY] at hf hb
  have hsplit := Proof.Hmac.Common.bytesAt_add u.mem (L.B + BitVec.ofNat 64 240) (P.Q - min P.H.D P.Q) (min P.H.D P.Q)
  rw [show P.Q - min P.H.D P.Q + min P.H.D P.Q = P.Q by omega, Offset.add_add,
    show 240 + (P.Q - min P.H.D P.Q) = 24 + (216 + (P.Q - min P.H.D P.Q)) by omega, hb, add_ofNat_zero] at hsplit
  rw [hsplit]
  unfold xOfDg
  have hdg : Spec.Sha256.bytesAt t.mem L.dg (min P.H.D P.Q) = (Spec.Sha256.bytesAt t.mem L.dg P.H.D).take P.Q := by
    by_cases h : P.H.D ≤ P.Q
    · rw [Nat.min_eq_left h, List.take_of_length_le (by rw [hl]; exact h)]
    · rw [Nat.min_eq_right (by omega), ← bytesAt_take _ _ (by omega)]
  rw [hl, hdg]
  refine congrArg (· ++ (Spec.Sha256.bytesAt t.mem L.dg P.H.D).take P.Q) ?_
  rw [bytesAt_frame hf (p := L.B + BitVec.ofNat 64 240) (n := P.Q - min P.H.D P.Q) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by nums)) (by omega)]
  have := zeros_sub hz (a := 0) (n := P.Q - min P.H.D P.Q) (by omega)
  rwa [add_ofNat_zero] at this

/-- The digest's copies, if `wide`: `Y`'s `Q` bytes are the digest between
`Q - D - 1` zero bytes and one, and `h`'s the digest after `Q - D`. -/
theorem prepCaseW_ok (hL : L.Ok) (hW : P.R.wide = true) {t : State} (hc : Ctx L g m₀ t) (hdn : P.H.D ≤ dn)
    (hsi : t.gpr .rsi = L.dg) (hz : Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 240) 144 = List.replicate 144 0) :
    WP isa (.block ((cfgOf P).prepCase P.H.D)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 240, 144⟩] t.mem t'.mem ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 240) P.Q =
        List.replicate (P.Q - P.H.D - 1) 0 ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D ++ [0] ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 312) P.Q =
        List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D := by
  obtain ⟨hw9, hQ66⟩ := P.sizesW hW
  have he := L.he
  have hD64 : P.H.D ≤ 64 := by nums
  have hD20 : 20 ≤ P.H.D := by nums
  have e : (cfgOf P).prepCase P.H.D = Cfg.copyBytes P.H.D .rsi 0 .rsp (216 + (P.Q - P.H.D - 1)) ++
      Cfg.copyBytes P.H.D .rsi 0 .rsp (288 + (P.Q - P.H.D)) := by
    simp only [Cfg.prepCase, cfgOf, hW, ite_true, fY, fH]
  rw [e, WP.block_append_iff]
  have dgS : ∀ {d : Nat}, 24 + d + P.H.D ≤ 520 →
      Region.Disjoint ⟨L.dg + BitVec.ofNat 64 0, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (24 + d), P.H.D⟩ := fun h => by
    rw [add_ofNat_zero]
    exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hdn)
  refine WP.mono (copyBF_ok hL hc (S := L.dg) hsi (by decide) (so := 0) (by omega) (by omega) (by omega) (by omega)
    (fun j hj => by rw [Nat.zero_add]; exact hc.inDg (by omega) (by omega)) (dgS (by omega)))
    fun u₁ ⟨hc₁, hg₁, hf₁, hb₁⟩ => ?_
  have hsi₁ : u₁.gpr .rsi = L.dg := (hg₁ _ (by decide)).trans hsi
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt t.mem L.dg P.H.D :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_DG (by omega)).symm.sub_left (Region.sub_prefix hdn)) (by omega)
  refine WP.mono (copyBF_ok hL hc₁ (S := L.dg) hsi₁ (by decide) (so := 0) (by omega) (by omega) (by omega) (by omega)
    (fun j hj => by rw [Nat.zero_add]; exact hc₁.inDg (by omega) (by omega)) (dgS (by omega)))
    fun u₂ ⟨hc₂, hg₂, hf₂, hb₂⟩ => ⟨hc₂, ?_, fun r hr => (hg₂ r hr).trans (hg₁ r hr), ?_, ?_⟩
  · refine (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)
  · -- `Y`: zeros, the digest, a zero.
    have k₂ : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q =
        Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 240) P.Q :=
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    have z₁ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 240) (P.Q - P.H.D - 1) =
        List.replicate (P.Q - P.H.D - 1) 0 := by
      rw [bytesAt_frame hf₁ (p := L.B + BitVec.ofNat 64 240) (n := P.Q - P.H.D - 1) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      have := zeros_sub hz (a := 0) (n := P.Q - P.H.D - 1) (by omega)
      rwa [add_ofNat_zero] at this
    have z₂ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (240 + (P.Q - 1))) 1 = [0] := by
      rw [bytesAt_frame hf₁ (p := L.B + BitVec.ofNat 64 (240 + (P.Q - 1))) (n := 1) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
      have := zeros_sub hz (a := P.Q - 1) (n := 1) (by omega)
      rwa [Offset.add_add] at this
    rw [k₂, show P.Q = (P.Q - P.H.D - 1) + P.H.D + 1 by omega, Proof.Hmac.Common.bytesAt_add,
      Proof.Hmac.Common.bytesAt_add, Offset.add_add, Offset.add_add,
      show (P.Q - P.H.D - 1) + P.H.D + 1 - P.H.D - 1 = P.Q - P.H.D - 1 by omega,
      show 240 + (P.Q - P.H.D - 1) = 24 + (216 + (P.Q - P.H.D - 1)) by omega, hb₁, add_ofNat_zero,
      show 240 + (P.Q - P.H.D - 1 + P.H.D) = 240 + (P.Q - 1) by omega, z₁, z₂]
  · -- `h`: zeros, the digest.
    rw [show P.Q = (P.Q - P.H.D) + P.H.D by omega, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      show 312 + (P.Q - P.H.D) = 24 + (288 + (P.Q - P.H.D)) by omega, hb₂, add_ofNat_zero, hdg₁,
      show (P.Q - P.H.D) + P.H.D - P.H.D = P.Q - P.H.D by omega]
    refine congrArg (· ++ Spec.Sha256.bytesAt t.mem L.dg P.H.D) ?_
    rw [bytesAt_frame hf₂ (p := L.B + BitVec.ofNat 64 312) (n := P.Q - P.H.D) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
      bytesAt_frame hf₁ (p := L.B + BitVec.ofNat 64 312) (n := P.Q - P.H.D) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    have := zeros_sub hz (a := 72) (n := P.Q - P.H.D) (by omega)
    rwa [Offset.add_add] at this

end VG.Proof.Ecdsa.Rfc6979.X86_64
