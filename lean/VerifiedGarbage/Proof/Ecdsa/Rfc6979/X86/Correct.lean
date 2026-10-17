module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Loop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.NoSp
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# Deterministic ECDSA on x86 (32-bit): correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, the hash function's sizes and `X` (`stageA_ok`), and `h`, `K`, `V`,
`core`'s digest and the count are as RFC 6979's steps a–g make them
(`stageB_ok` … `stageE_ok`); and the signature of that candidate is RFC
6979's (`result_eq`), for the instance of the run `P.I` (the contract's,
with the hash function the argument `hash` names).
The frame's allocation, our caller's registers saved and restored, and the
return address kept give the whole function (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : Fits P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega, hc', ?_, by omega⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega) (by show 8 * P.R.E.C.len < _; omega)

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
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOf P L u.mem = List.replicate P.F.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- What depends on the hash function: its sizes and `X`, through the dispatch. -/
theorem stageA_ok (hL : L.Ok) (hk : Fits P L) {u : State} (hc : Ctx0 L g m₀ u) (hsi : u.gpr .esi = L.a2)
    (hbx : u.gpr .ebx = L.hs) :
    WP isa (cfgOf P).setup u fun u' => Ctx L g m₀ u' ∧ XOk P L m₀ u'.mem :=
  WP.mono (setup_ok hL hk hc hsi hbx) fun _ ⟨h₁, _, h₃⟩ => ⟨h₁, h₃⟩

theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hx : XOk P L m₀ u.mem) :
    WP isa (cfgOf P).prep u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' :=
  WP.mono (prep_ok hL hc hx) fun _ ⟨h₁, _, h₃⟩ => ⟨h₁, h₃.h, h₃.k _ (by nums), h₃.v _ (by nums), h₃.x⟩

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m := by
  have nB := hL.nB
  refine bytesAt_frame hf (fun r hr => ?_) (by nums)
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hL.stk_SCR (by nums)
  · exact Offset.disjoint_base _ (by omega) (by nums)

theorem stageC_ok (hL : L.Ok) (hk : Fits P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨(hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.q])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.q])], hq.dg.frameOf hL hf' kvw_apart⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : Fits P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk hc 1) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.q])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.q])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hf' (by simp [DgApart])⟩

theorem stageG_ok (hL : L.Ok) (hk : Fits P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' ∧
      ∀ p ∈ saved, u'.gpr p.1 = g p.1 :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇, hs₇⟩ => ⟨hc₇, ⟨hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega)).symm.sub_left (Region.sub_prefix (by rw [hk.q]))
      · exact (hL.stk_OUT (by omega)).symm.sub_left (Region.sub_prefix (by rw [hk.q]))) (by nums))⟩, hs₇⟩

/-- `hash` in `ebx`, and `digest` in `esi`. -/
theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx0 L g m₀ t) :
    WP isa (.block (selArg ++ digestPtr)) t fun u => Ctx0 L g m₀ u ∧ u.gpr .esi = L.a2 ∧ u.gpr .ebx = L.hs := by
  refine VG.Proof.Mont.X86.wp_movS (hc.readArg hL (i := 5) (by decide)) fun u₁ v₁ _ =>
    VG.Proof.Mont.X86.wp_movS ((hc.regs hL v₁.rd v₁.wr v₁.mem (v₁.other _ (by decide)) v₁.syms).readArg hL (i := 2)
      (by decide)) fun u₂ v₂ _ => WP.block_nil ⟨?_, v₂.gpr, by rw [v₂.other _ (by decide), v₁.gpr]; rfl⟩
  exact (hc.regs hL v₁.rd v₁.wr v₁.mem (v₁.other _ (by decide)) v₁.syms).regs hL v₂.rd v₂.wr v₂.mem
    (v₂.other _ (by decide)) v₂.syms

/-- The body, after our caller's registers are saved. -/
theorem rest_ok (hL : L.Ok) (hk : Fits P L) {t : State} (hc : Ctx0 L g m₀ t) :
    WP isa (.block (selArg ++ digestPtr)) t fun u =>
      WP isa (.seq (cfgOf P).setup (.seq (cfgOf P).prep
        (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne .ne) (.block wipe))))))) u
      fun t' => Ctx L g m₀ t' ∧ (∃ i, Exit P L m₀ i t') ∧ ∀ p ∈ saved, t'.gpr p.1 = g p.1 :=
  WP.mono (start_ok hL hc) fun _ ⟨h₀, hsi, hbx⟩ =>
    WP.seq (WP.mono (stageA_ok hL hk h₀ hsi hbx) fun _ ⟨h₁, x₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ x₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (loop_ok hL hk h₅ q₅) fun _ ⟨h₆, i, q₆⟩ =>
              WP.mono (stageG_ok hL hk h₆ q₆) fun _ ⟨h₇, q₇, s₇⟩ => ⟨h₇, ⟨i, q₇⟩, s₇⟩))))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate, or two if `wide`. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nb := by
  have hl := P.R.nBits_len
  rw [Spec.Ecdsa.Rfc6979.blocks, RfcHash.nb, show 8 * P.Q - P.R.sh = Spec.Ecdsa.nBits P.R.E.C by
    show 8 * P.R.E.C.len - _ = _; omega]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega]
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
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.hH.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · rw [show P.I.tries - 1 - i = 0 by omega]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega) (by omega)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega

/-! ## The whole function -/

theorem released_gpr {s₂ : State} {r : Reg} (hr : r ≠ .esp) : (released s₂).gpr r = s₂.gpr r :=
  (Wp.Upd.setReg s₂ .esp _).other r hr

theorem released_esp (s₂ : State) : (released s₂).gpr .esp = s₂.gpr .esp + BitVec.ofNat 32 460 :=
  (Wp.Upd.setReg s₂ .esp _).gpr

/-- The layout of a run from `s`. -/
abbrev layP (P : RfcHash) (s : State) : Lay P.I.hashLen := layOf P.I P.F.H.B P.nb s P.R.E.combConsts

theorem fits_lay (P : RfcHash) {s : State} (h : (rfcX86 P.I P.k 536 P.R.E.combConsts).pre s) : Fits P (layP P s) :=
  ⟨P.curveLen, rfl, rfl, rfl, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- `vg_ecdsa_<curve>_rfc6979_sign` meets `rfcX86 P.I P.k` and keeps the
callee-saved registers and its return address. -/
theorem sign_ok {s : State} (h : (rfcX86 P.I P.k 536 P.R.E.combConsts).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcX86 P.I P.k 536 P.R.E.combConsts).post s s' := by
  have hL := lay_ok (Bk := P.F.H.B) (nb := P.nb) h
  have nB := hL.nB
  refine WP.alloc (by have := h.1; omega) (body_nosp P) (WP.seq ?_)
  rw [List.append_assoc]
  refine save_ok (Bk := P.F.H.B) (nb := P.nb) h fun t hc _ => WP.mono (rest_ok hL (fits_lay P h) hc) fun u hu =>
    hu.mono ?_
  intro u' ⟨hc', ⟨i, hx⟩, hs'⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [released_gpr (by decide)]; exact hs' (.ebx, 180) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.esi, 184) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.edi, 188) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.ebp, 192) (by decide)
    · rw [released_esp, hc'.esp]; exact BitVec.sub_add_cancel _ _
  · have hret : (s.gpr .esp).setWidth 64 = (layP P s).B + BitVec.ofNat 64 536 := by
      rw [hL.B_eq, BitVec.sub_add_cancel]; rfl
    show u'.mem.readW _ 32 = _
    rw [hret]
    refine hc'.frame.readW (r := (layP P s).RET) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.ro
    · exact hL.rc
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · show match (result P.I s.mem (layP P s).d (layP P s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [show P.I.ecdsa = P.I₀.ecdsa from rfl, P.ecdsa, P.R.curve]
    rw [e₁]
    have hr := hx.res
    have ha : (released u').gpr .eax = u'.gpr .eax := released_gpr (by decide)
    revert hr
    cases sigI P (layP P s) s.mem i with
    | some rs => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, by rw [e₂]; exact h₂⟩
    | none => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, h₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86
