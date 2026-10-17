module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Loop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Spec.Rc2

/-!
# Deterministic ECDSA on 32-bit ARM: correctness

As on x86 (`Proof/Ecdsa/Rfc6979/X86/Correct.lean`): the loop leaves it at a
candidate that is suitable or the last (`loop_ok`); before it, `h`, `K`,
`V`, `core`'s digest and the count are as RFC 6979's steps a–g make them
(`stageB_ok` … `stageE_ok`); and the signature of that candidate is RFC
6979's (`result_eq`), for the run's hash function `P`. The frame's
allocation, the prologue (our caller's registers saved in the frame, the
stack arguments loaded, the hash function's code computed), and the
registers restored give the whole function (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)
open VG.Proof.X25519.Arm (Upd wp_mov wp_dp op2_reg op2_imm op2_lsr dpVal)

variable {P : RfcHash} {L : Lay P.F.H.D} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.R.I.tries - n) s ∧
    n ≤ P.R.I.tries) ?_ P.R.I.tries t ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_arith
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_arith, hc', ?_, by omega_arith⟩
    rwa [show P.R.I.tries - (n - 1) = P.R.I.tries - n + 1 by omega_arith]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by show 8 * P.R.E.C.len < _; omega_arith)

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D x hB =
      let K₁ := P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.F.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ (State.addr L.d) P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) (u : State) : Prop where
  h : hOfP P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOfP P L u.mem = List.replicate P.F.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) (u : State) : Prop where
  h : hOfP P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOfP P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOfP P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem

theorem kv0_eq' (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- After steps a and b: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) (u : State) : Prop where
  h : hOfP P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- Steps a and b: `h` and `core`'s digest. -/
theorem stageA_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) (h10 : u.gpr .r10 = L.dg) :
    WP isa (cfgOf P).digest u fun u' => Ctx L g m₀ u' ∧ QA P L m₀ u' :=
  WP.mono (digest_ok hL hk rfl hc h10) fun _ ⟨hc₁, _, hh₁, hdg₁⟩ => ⟨hc₁, hh₁, hdg₁⟩

/-- Step c: `V = 0x01…` and `K = 0x00…`. -/
theorem initKV_stage (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QA P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hb := hL.B_fit
  have hQ' := P.wsizes
  have hD := P.sizes
  refine WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), ?_⟩
  · refine Eq.trans ?_ hq.h
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega)
  · exact hq.dg.frame hf₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      unfold dgAddr; split
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

/-- Steps a–c: `h`, `core`'s digest, `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) (h10 : u.gpr .r10 = L.dg)
    {p : Prog isa} {Q : State → Prop} (hQ : ∀ u', Ctx L g m₀ u' → QB P L m₀ u' → WP isa p u' Q) :
    WP isa (.seq (cfgOf P).digest (.seq (.block Cfg.initKV) p)) u Q :=
  WP.seq (WP.mono (stageA_ok hL hk hc h10) fun _ ⟨hc₁, hq₁⟩ =>
    WP.seq (WP.mono (initKV_stage hL hc₁ hq₁) fun u₂ ⟨hc₂, hq₂⟩ => hQ u₂ hc₂ hq₂))

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOfP P L m' = hOfP P L m := by
  have hb := hL.B_fit
  have hQ := P.wsizes
  refine bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

theorem stageC_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk hc (b := 0) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', (hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk hc (b := 1) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageE_ok {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok (P := P) hc) fun u' ⟨hc', hm', hn'⟩ => ⟨hc', P.R.tries_pos, hm' ▸ hq.k, hm' ▸ hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hm' ▸ hq.dg⟩

/-- After the wiping: the result, and our caller's registers. -/
structure Fin (P : RfcHash) (L : Lay P.F.H.D) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) : Prop where
  wr : u.wr = [L.FR, L.OUT, L.SCR]
  sp : u.sp = L.fp
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, u.gpr p.1 = g p.1
  exit : ∃ i, Exit P L m₀ i u

theorem stageG_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u (Fin P L g m₀) := by
  have := hL.B_fit
  have hQ := P.wsizes
  exact WP.mono (wipe_ok hL hc) fun _ ⟨_, hwr, hsp, hs, ha, hf⟩ => ⟨hwr.trans hc.wr, hsp.trans hc.sp, hs, i,
    hx.lt, hx.fails, hx.last, hx.res.keep ha (bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by anums))⟩

/-- The body, after `h`, `V` and `K`. -/
theorem rest_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) (hq : QB P L m₀ t) :
    WP isa (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne .ne) (.block Cfg.wipe))))) t (Fin P L g m₀) :=
  WP.seq (WP.mono (stageC_ok hL hk hc hq) fun _ ⟨h₂, q₂⟩ =>
    WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
      WP.seq (WP.mono (stageE_ok h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
        WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, _, q₅⟩ => stageG_ok hL hk h₅ q₅))))

/-! ## RFC 6979's result -/

/-- RFC 6979's signature and number of candidates, with the run's hash function. -/
abbrev result (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) : Option (Nat × Nat) × Nat :=
  Spec.Ecdsa.Rfc6979.sign P.R.E.C P.ok.hH.SH.H P.F.H.D P.R.I.tries (xOf P L m₀) (hBOf P L m₀)

/-- The signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P L m₀ =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V P.R.I.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) : (result P L m₀).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.R.I.tries (by have := hx.lt; omega_arith) hx.fails,
      show P.R.I.tries - i = (P.R.I.tries - 1 - i) + 1 by have := hx.lt; omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.R.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.R.I.tries - 1 - i = 0 by omega]
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
def exitAt (P : RfcHash) (L : Lay P.F.H.D) (m₀ : Mem) : Nat :=
  if (result P L m₀).2 = 0 then P.R.I.tries - 1 else (result P L m₀).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.R.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.R.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.R.I.tries (by omega_arith) hf,
      show P.R.I.tries - i = (P.R.I.tries - 1 - i) + 1 by omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.R.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.R.I.tries - 2 - i)
          (K := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.R.I.tries - 1 - i = P.R.I.tries - 2 - i + 1 by omega_arith]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega_arith
      · rw [show P.R.I.tries - 1 - i = 0 by omega_arith]
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

/-- Words stored at offsets apart from a range below them change nothing outside it. -/
theorem Outs.frame {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {n : Nat}
    (h : VG.Proof.Mont.Outs base rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ n) : Frame [⟨base, n⟩] m m' :=
  fun x hx => h x fun r hr' => .inr (by
    have := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at this
    simp only [VG.Proof.Mont.ofs]
    have := hr r hr'; omega_arith)

theorem saved_ne12 : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, p.1 ≠ .r12 := by decide

theorem saved_pairwise : Impl.Ecdsa.Rfc6979.Arm.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  decide

/-- The prologue: our caller's registers into the frame, the stack arguments
loaded, the pointers moved to the registers that keep them, and the hash
function's code computed. -/
theorem entry_ok {I : Spec.Ecdsa.Rfc6979.Instance} {dn : Nat} {s : State} (h : (rfcArm I 456).pre s)
    (hd : (s.gpr .r3).toNat = dn) :
    WP isa (.block Cfg.prologue) (allocated frameBytes s) fun t =>
      Ctx (lay dn I.ecdsa.curve.len s) s.gpr s.mem t ∧ t.gpr .r10 = s.gpr .r2 := by
  have hL := lay_ok' h hd
  obtain ⟨hrd, hwr, -⟩ := h
  have hA : State.addr (lay dn I.ecdsa.curve.len s).fp = (lay dn I.ecdsa.curve.len s).B + BitVec.ofNat 64 24 :=
    hL.fpA0
  have hb := hL.B_fit
  have hn : s.sp.toNat + 8 ≤ 2 ^ 32 := hL.nA
  have hn' : 456 ≤ s.sp.toNat := hL.nB
  simp only [Cfg.prologue, List.cons_append, frameBytes, Nat.reduceAdd]
  refine wp_addSp (d := .r12) (imm := 0) (by decide) fun u₁ v₁ => ?_
  have h12 : u₁.gpr .r12 = (lay dn I.ecdsa.curve.len s).fp := by rw [v₁.gpr, BitVec.add_zero]; rfl
  have hs : VG.Proof.Mont.Arm.Scr u₁ (State.addr (lay dn I.ecdsa.curve.len s).fp) 432 :=
    ⟨by rw [h12], ⟨432, Nat.le_refl _, by decide, by rw [v₁.wr]; exact List.mem_cons_self⟩,
      by rw [hA, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith, by decide⟩
  rw [WP.block_append_iff]
  refine WP.mono (Proof.Weierstrass.Arm.strs_ok hs _ (fun p hp => (saved_off p hp).2) saved_pairwise)
    fun u₂ ⟨K₂, O₂, V₂⟩ => ?_
  -- What the saves wrote: the frame, apart from the arguments on the stack.
  have hf₂ : Frame [(lay dn I.ecdsa.curve.len s).FR] s.mem u₂.mem := by
    rw [show s.mem = u₁.mem from v₁.mem.symm]
    refine (Outs.frame O₂ (n := 432) fun r hr => ?_).sub fun r hr => ?_
    · simp only [List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact (saved_off q hq).2
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [hA]; exact sub_refl _⟩
  have hsp₂ : u₂.sp = s.sp - BitVec.ofNat 32 432 := by rw [K₂.sp, v₁.sp]; rfl
  have hrd₂ : u₂.rd = s.rd := by rw [K₂.rd, v₁.rd]; rfl
  have hfa : (lay dn I.ecdsa.curve.len s).FR.Disjoint (lay dn I.ecdsa.curve.len s).ARGS :=
    hL.stk_args (d := 24) (n := 432) (by omega)
  have ha0 : State.addr (s.sp + BitVec.ofNat 32 (4 * 0)) = State.addr s.sp := by
    simp only [Nat.mul_zero, BitVec.add_zero]
  have hfa' : Region.Disjoint (lay dn I.ecdsa.curve.len s).FR ⟨State.addr s.sp, 8⟩ := by
    have : (lay dn I.ecdsa.curve.len s).ARGS = ⟨State.addr s.sp, 8⟩ := by
      simp only [Lay.ARGS, lay]; rw [ha0]
    rw [← this]; exact hfa
  have hargs : ∀ {o : Nat}, o + 4 ≤ 8 → InRegions (u₂.rd ++ u₂.wr) (State.addr s.sp + BitVec.ofNat 64 o) 4 :=
    fun ho => ⟨⟨State.addr s.sp, 8⟩, by
      rw [hrd₂, hrd]
      refine List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
      simp only [stackArgAddr, List.mem_singleton]; rw [ha0], Offset.contains_base _ ho (by omega)⟩
  have hrw : ∀ {o : Nat}, o + 4 ≤ 8 →
      u₂.mem.readW (State.addr s.sp + BitVec.ofNat 64 o) 32 = s.mem.readW (State.addr s.sp + BitVec.ofNat 64 o) 32 :=
    fun ho => hf₂.readW (r := ⟨State.addr s.sp, 8⟩) (Offset.contains_base _ ho (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hfa'.symm) (by decide)
  have hspA : ∀ {o : Nat}, o < 8 →
      State.addr (u₂.sp + BitVec.ofNat 32 (432 + o)) = State.addr s.sp + BitVec.ofNat 64 o := fun ho => by
    rw [hsp₂, ← addr_add (by omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine wp_ldrSp (a := State.addr s.sp + BitVec.ofNat 64 0) (by decide) (hspA (o := 0) (by decide)) (hargs (by decide)) fun u₃ v₃ => ?_
  refine wp_ldrSp (a := State.addr s.sp + BitVec.ofNat 64 4) (by decide) (by rw [v₃.sp]; exact hspA (o := 4) (by decide))
    (by rw [v₃.rd, v₃.wr]; exact hargs (by decide)) fun u₄ v₄ => ?_
  refine wp_mov (op2_reg _ _) fun u₅ v₅ => wp_mov (op2_reg _ _) fun u₆ v₆ => ?_
  refine wp_mov (op2_reg _ _) fun u₇ v₇ => wp_mov (op2_reg _ _) fun u₈ v₈ => ?_
  refine wp_dp (op2_imm (by decide)) fun u₉ v₉ => wp_mov (op2_lsr (by decide)) fun u₁₀ v₁₀ => ?_
  refine wp_dp (op2_reg _ _) fun u₁₁ v₁₁ => WP.block_nil ?_
  have hm : u₁₁.mem = u₂.mem := by
    rw [v₁₁.mem, v₁₀.mem, v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem]
  have g₂ : ∀ r, r ≠ .r12 → u₂.gpr r = s.gpr r := fun r hr => by rw [K₂.gpr r (by simp), v₁.other _ hr]; rfl
  have hsa : ∀ i, i < 2 → stackArg s i = u₂.mem.readW (State.addr s.sp + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi => by
      rw [hrw (by omega), stackArg, stackArgAddr, addr_add (by omega)]
  have e₀ := hsa 0 (by decide)
  have e₁ := hsa 1 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero] at e₀ e₁
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun p hp => ?_, ?_⟩, ?_⟩
  · rw [v₁₁.rd, v₁₀.rd, v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, hrd₂, hrd, hd]; rfl
  · rw [v₁₁.wr, v₁₀.wr, v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, K₂.wr, v₁.wr]
    show ⟨State.addr (lay dn I.ecdsa.curve.len s).fp, 432⟩ :: s.wr = _
    rw [hA, hwr]
    rfl
  · rw [v₁₁.sp, v₁₀.sp, v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, hsp₂]; rfl
  · simp (disch := decide) only [v₁₁.other, v₁₀.other, v₉.other, v₈.other, v₇.other, v₆.other, v₅.gpr]
    rw [v₄.other _ (by decide), v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · simp (disch := decide) only [v₁₁.other, v₁₀.other, v₉.other, v₈.other, v₇.other, v₆.gpr]
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · simp (disch := decide) only [v₁₁.gpr, v₁₀.gpr, v₁₀.other, v₉.gpr, v₉.other, v₈.other, v₇.other, v₆.other,
      v₅.other, v₄.gpr, dpVal]
    rw [v₄.other _ (by decide), v₃.other _ (by decide), g₂ _ (by decide), v₃.mem, ← e₁]
    rfl
  · simp (disch := decide) only [v₁₁.other, v₁₀.other, v₉.other, v₈.gpr]
    rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), K₂.gpr _ (by simp), h12]
  · simp (disch := decide) only [v₁₁.other, v₁₀.other, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other,
      v₄.other, v₃.gpr]
    rw [BitVec.add_zero]; exact e₀.symm
  · rw [hm, ← Offset.add_add, ← hA, ← VG.Proof.Mont.off, V₂ p hp, v₁.other _ (saved_ne12 p hp)]; rfl
  · rw [hm]
    exact hf₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨(lay dn I.ecdsa.curve.len s).STK, by simp, Offset.sub_base _ (by omega)⟩
  · simp (disch := decide) only [v₁₁.other, v₁₀.other, v₉.other, v₈.other, v₇.gpr]
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      g₂ _ (by decide)]

theorem low_preserved : ∀ r ∈ preserved, r ∈ Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst := by decide

/-- The code `r6` holds is the hash function's. -/
theorem hOk_lay {s : State} (hD : (s.gpr .r3).toNat = P.F.H.D) (hk : (stackArg s 1).toNat = P.k) :
    HOk P (lay P.F.H.D P.R.I.ecdsa.curve.len s) := by
  refine ⟨P.curveLen, ?_⟩
  show s.gpr .r3 + (stackArg s 1 + BitVec.ofNat 32 4) >>> 3 = BitVec.ofNat 32 P.c
  apply BitVec.eq_of_toNat_eq
  have := P.hk; have := P.blk; have := P.sizes
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hD, hk,
    RfcHash.c, code]
  omega

/-- The result `rfcArm` names, for the hash function `P`. -/
theorem anyResult_eq {s : State} (hD : (s.gpr .r3).toNat = P.F.H.D) (hk : (stackArg s 1).toNat = P.k) :
    anyResult P.R.I s = some (result P (lay P.F.H.D P.R.I.ecdsa.curve.len s) s.mem) := by
  have e₂ : P.R.I.ecdsa.curve = P.R.E.C := by rw [P.R.ecdsa, P.R.curve]
  simp only [anyResult, Spec.Ecdsa.Rfc6979.Instance.anyResult, hk, P.hash, Option.map_some, hD, e₂]
  rfl

/-- The digest's length is the hash function's. -/
theorem digestLen_eq {s : State} (h : (rfcArm P.R.I 456).pre s) (hk : (stackArg s 1).toNat = P.k) :
    (s.gpr .r3).toNat = P.F.H.D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hm⟩ := h
  obtain ⟨H, hH, hl⟩ := P.len
  rw [← hl]; exact hm H (by rw [hk]; exact hH)

/-- `vg_ecdsa_<curve>_rfc6979_sign` with the hash function `P` meets
`rfcArm` and keeps the callee-saved registers and the stack pointer. -/
theorem sign_ok {s : State} (h : (rfcArm P.R.I 456).pre s) (hk : (stackArg s 1).toNat = P.k) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcArm P.R.I 456).post s s' := by
  have hD := digestLen_eq h hk
  have hL := lay_ok' h hD
  have hO := hOk_lay hD hk
  have hb : 432 ≤ s.sp.toNat := by have h1 : 456 ≤ s.sp.toNat := hL.nB; omega
  show WP isa (.frame (.alloc frameBytes) (cfgOf P).body (.free frameBytes)) s _
  refine WP.alloc (by decide) hb ?_
  unfold Cfg.body
  refine WP.seq (WP.mono (entry_ok h hD) fun t ⟨hc, h10⟩ => ?_)
  refine stageB_ok hL hO hc h10 fun u hu hq => ?_
  refine WP.mono (rest_ok hL hO hu hq) fun v ⟨hwr, hsp, hs, i, hx⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show v.gpr r = _
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (low_preserved r hr)
    exact hs p hp
  · show v.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hsp]; exact BitVec.sub_add_cancel _ _
  · have e₁ : 2 * P.R.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.R.I.ecdsa.curve = P.R.E.C := by rw [P.R.ecdsa, P.R.curve]
    show match anyResult P.R.I s with | some (some rs, _) => _ | _ => _
    rw [anyResult_eq hD hk, show result P (lay P.F.H.D P.R.I.ecdsa.curve.len s) s.mem =
      ((result P (lay P.F.H.D P.R.I.ecdsa.curve.len s) s.mem).1,
        (result P (lay P.F.H.D P.R.I.ecdsa.curve.len s) s.mem).2) from rfl, result_eq hx]
    have hr := hx.res
    unfold ResultIs at hr
    cases hsig : sigI P (lay P.F.H.D P.R.I.ecdsa.curve.len s) s.mem i <;> rw [hsig] at hr <;>
      dsimp only at hr ⊢ <;> rw [e₁] <;> (try rw [e₂]) <;> exact ⟨by rw [low_word]; exact hr.1, hr.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
