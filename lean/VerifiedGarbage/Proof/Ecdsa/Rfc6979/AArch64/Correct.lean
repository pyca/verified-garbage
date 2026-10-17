module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Loop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy

/-!
# Deterministic ECDSA on AArch64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V`, `core`'s digest and the count are as RFC 6979's
steps a–g make them (`start_ok`, `stageC_ok` … `stageE_ok`); and the
signature of that candidate is RFC 6979's (`result_eq`), for the hash
function `P`'s instance of the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne (.nonzero .x .x12)) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_arith
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_arith, hc', ?_, by omega_arith⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_arith]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by show 8 * P.R.E.C.len < _; omega_arith)

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D x hB =
      let K₁ := P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

abbrev dB (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.H.D 1)

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : tailOf P L u.mem = dB P L m₀ ++ hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- `d ‖ h` in the messages, kept by the steps on `K` and `V`. -/
theorem tailOf_kvw (hL : L.Ok) (hk : CoreOk P L) {m m' : Mem} (hf : Frame (KVW L) m m') :
    tailOf P L m' = tailOf P L m := by
  have nB := hL.nB
  have hs := P.wsizes
  have hdk : ∀ r ∈ KVW L, Region.Disjoint ⟨L.d, P.Q⟩ r := fun r hr => by
    have hD : Region.Sub ⟨L.d, P.Q⟩ L.D := Region.sub_prefix (by rw [hk.1])
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.dc.sub_left hD
    · exact (hL.kd.symm.sub_left hD).sub_right (Region.sub_prefix (by omega_arith))
  refine congrArg₂ (· ++ ·) (bytesAt_frame hf hdk (by omega_arith)) (bytesAt_frame hf (fun r hr => ?_) (by omega_arith))
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hL.stk_SCR (by omega_arith)
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' := by
  have ht : tailOf P L u.mem = dB P L m₀ ++ hSpec P L m₀ := by
    rw [tailOf, hc.dBytes hL (by rw [hk.1]), hq.h]
  exact WP.mono (rekeyFull_ok hL hk.1 rfl hk.2 hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', (tailOf_kvw hL hk hf').trans ht, by rw [hk', hq.k, hq.v, ht],
      by rw [hv', hk', hq.k, hq.v, ht], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.1 rfl hk.2 hc 1) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h], by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h],
      hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageE_ok (hL : L.Ok) (_hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _),
    hq.dg.frameOf hL hf' fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [DgApart]⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' := by
  have := hL.nB
  exact WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by anums))⟩

/-- The frame's body, once the arguments are saved. -/
theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (cfgOf P).start
      (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12))
        (.block Cfg.wipe)))))) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (start_ok hL hk hc) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageC_ok hL hk h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageE_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
            WP.mono (stageG_ok hL hk h₅ q₅) fun _ ⟨h₆, q₆⟩ => ⟨h₆, i, q₆⟩)))))

/-! ## RFC 6979's result -/

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, ← P.v.hSH,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift rfl i P.I.tries (by have := hx.lt; omega_arith) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok rfl hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail rfl hs, show P.I.tries - 1 - i = 0 by omega]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift rfl i P.I.tries (by omega_arith) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok rfl hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail rfl hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.SH.H) (hlen := P.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) rfl
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_arith]
        simp only [true_and, h7]
        simp only [kvI, RfcHash.nb] at this ⊢
        rw [true_iff]
        split <;> omega_arith
      · rw [show P.I.tries - 1 - i = 0 by omega_arith]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega) (by omega)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_arith

/-! ## The whole function -/

/-- RFC 6979's result for the instance of `P`'s hash function, as the
function returns and writes it. -/
def postK (P : RfcHash) (s s' : State) : Prop :=
  match (result P.I s.mem (s.gpr .x1) (s.gpr .x2)).1 with
  | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s.gpr .x0) (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
  | none => (s'.gpr .x0).setWidth 32 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s.gpr .x0) (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- The digest's length is `P`'s hash function's. -/
theorem dlen_of (P : RfcHash) {s : State} (h : (rfcAArch64 P.R.E P.J 512).pre s) (hs : selOf s = P.k) :
    (s.gpr .x3).toNat = P.H.D :=
  (h.2.1 _ (by rw [hs, ← P.mgfFn])).trans P.v.mgf.len

theorem coreOk_lay (P : RfcHash) (s : State) (hs : selOf s = P.k) :
    CoreOk P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E s) :=
  ⟨P.curveLen, hs, by show blOf (selOf s) = _; rw [hs, P.bl_eq]⟩

/-- `vg_ecdsa_<curve>_rfc6979_sign` with the hash function of `P` meets
`rfcAArch64 P.R.E P.J`'s precondition, gives `P`'s result, and keeps the
callee-saved registers and the stack pointer. -/
theorem sign_ok {s : State} (h : (rfcAArch64 P.R.E P.J 512).pre s) (hs : selOf s = P.k) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      postK P s s' := by
  have hdn := dlen_of P h hs
  have hL := lay_ok (dn := P.I.hashLen) h hdn
  have hN : 512 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk := coreOk_lay P s hs
  refine WP.frame (by omega_arith) (WP.alloc ⟨by decide, by decide, by decide⟩ ?_ ?_)
  · show frameBytes ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 480 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (cfgOf P).body (entered s) _
    refine WP.seq (WP.mono (entry_ok h hdn) fun t hc => ?_)
    refine WP.mono (body_ok hL hk hc) fun u ⟨hu, i, hx⟩ => ?_
    have lr : u.mem.read (u.sp + BitVec.ofNat 64 frameBytes) 8 = s.gpr .x30 := by
      rw [hu.sp, Offset.add_add, read8, show 16 + frameBytes = 496 from rfl]; exact hu.lr
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [popped, freed, RegUpd.gpr_write, lr]
      by_cases h30 : r = .x30
      · subst r; simp only [ite_true, BitVec.setWidth_eq]
      · simp only [h30, ite_false]
        exact hu.cs r hr h30
    · show u.sp + BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 16 = s.sp
      rw [hu.sp, Offset.add_add, Offset.add_add, show 16 + (frameBytes + 16) = 512 from rfl]
      exact lay_top _ _ _ s
    · show match (result P.I s.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E s).d
          (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E s).dg).1 with
        | some rs => _ | none => _
      rw [result_eq hx]
      refine hx.res.keep (by simp only [popped, freed, RegUpd.gpr_write]; rfl) ?_
      simp only [popped, freed, RegUpd.mem_write]

end VG.Proof.Ecdsa.Rfc6979.AArch64
