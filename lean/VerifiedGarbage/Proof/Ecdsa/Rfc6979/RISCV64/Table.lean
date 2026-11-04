module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.CT
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Deterministic ECDSA on RISC-V: the hash function of a table

`vg_ecdsa_<curve>_sign` (`signCode`) loads the index of the hash function
from the table `hash` (its word 3) and runs the code for that index's
digest length and block size (`cfgT`), which calls the table's functions.
For the hash functions `vs` whose tables pass the registration's checks
(`OK`: their functions of the same name have the same code, and each is of
one of the hash functions with HMAC, of the sizes its index's code is for),
the table of each `w` makes it the code for `w`'s hash function (`rfcOf`),
which meets the contract with that hash function fixed (`correct`, `ct`).
`tabK` states that contract for whichever of the tables `hash` holds, on
entry; `TableSpec.lean` shows `TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG VG.RISCV64 VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.RISCV64.Steps (Upd wp_ld wp_subi)
open VG.Proof.HashTable.RISCV64 (TVar tables fnsOf names Coh tableOf mem_names)

/-! ## The code -/

/-- A curve's kit, with what the code for every hash function needs of it:
the scalars' bits are all their bytes', or the scalars are longer than any
hash function's output (P-521's); and the digest's bytes `core` reads are the
scalars', or at least any hash function's output. -/
structure RfcCurve where
  kit : Kit
  coreN : String
  hsh : kit.sh = 0 ∨ 64 < kit.Q
  hGQ : kit.G ≤ kit.Q
  hG8 : 8 * kit.G ≤ Spec.Ecdsa.nBits kit.E.curve
  hGD : kit.G = kit.Q ∨ (64 ≤ kit.G ∧ 64 < kit.Q)

/-- The code for a hash function of the digest length `D` and the block
size `B`, calling no table's functions. -/
def cfgS (R : RfcCurve) (tries D B : Nat) : Cfg where
  D := D
  B := B
  f := ⟨[], [], []⟩
  FN := R.kit.FN
  coreN := R.coreN
  coreC := R.kit.coreC
  tries := tries
  nw := R.kit.nw
  Q := R.kit.Q
  sh := R.kit.sh
  G := R.kit.G

/-- The code for the hash function of index `i`, with the tables of `vs`. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List TVar) (i : Nat) : Cfg :=
  { cfgS R tries (shapeOf i).1 (shapeOf i).2 with f := fnsOf vs }

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (R : RfcCurve) (tries : Nat) (vs : List TVar) : Prog isa := signT (cfgT R tries vs)

/-- The stack it uses: the most of any hash function's. -/
def stackT : Nat := 560

/-- The sizes of every index's code. -/
theorem shapeOf_ok (i : Nat) : 16 ≤ (shapeOf i).1 ∧ (shapeOf i).1 ≤ 64 ∧ (shapeOf i).1 % 4 = 0 ∧
    ((shapeOf i).2 = 64 ∨ (shapeOf i).2 = 128) := by
  unfold shapeOf; split <;> decide

/-! ## The hash functions -/

/-- What the code needs of a hash function `w`: it has HMAC (over `w`'s
block size), its index is one of the code's, and that index's code is for
`w`'s digest length and block size. -/
def WOk (w : TVar) : Prop :=
  (match Spec.Ecdsa.Rfc6979.hmacOf w.l.G with
    | some F => F.blockSize = w.H.B
    | none => False) ∧
  Spec.HashTable.index w.l.G < 8 ∧ shapeOf (Spec.HashTable.index w.l.G) = (w.H.D, w.H.B)

instance (w : TVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.Ecdsa.Rfc6979.hmacOf w.l.G <;> infer_instance

/-- What the registrations check of the hash functions whose tables the
function takes. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem labelHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.RsaOaep.RISCV64.labelHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.RsaOaep.RISCV64.labelHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Spec.Mgf1.hashes]

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : TVar} (hw : WOk w) : Spec.Ecdsa.Rfc6979.hmacOf w.l.G = some w.l.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.Ecdsa.Rfc6979.hmacOf w.l.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.Ecdsa.Rfc6979.hmacOf_hash _ (labelHashes_sub w.l.mem) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.l.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.l.hash x)⟩

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.l.ok.SH.H
  hashLen := w.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries
  scratchWords := T.scratchWords

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.kit.E
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2048

/-- The proof's instance: the code for `w`'s index, with `w`'s streaming
functions. -/
def rfcOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List TVar) (w : TVar)
    (hw : WOk w) : Rfc where
  c := cfgT R T.tries vs (Spec.HashTable.index w.l.G)
  w := w
  hDw := by show (shapeOf _).1 = _; rw [hw.2.2]
  hBw := by show (shapeOf _).2 = _; rw [hw.2.2]
  I := instOf T w
  kit := R.kit
  hE := hC.ecdsa
  hHash := rfl
  hD := by show w.H.D = (shapeOf _).1; rw [hw.2.2]
  hnw := rfl
  hQ := rfl
  hG := rfl
  hGw := fun h => by
    have hs := shapeOf_ok (Spec.HashTable.index w.l.G)
    have : R.kit.Q ≤ (shapeOf (Spec.HashTable.index w.l.G)).1 := by
      have h' : decide ((shapeOf (Spec.HashTable.index w.l.G)).1 < R.kit.Q) = false := h
      simpa using h'
    rcases R.hGD with e | ⟨-, e⟩
    · exact e
    · omega
  hGD := fun h => by
    have hs := shapeOf_ok (Spec.HashTable.index w.l.G)
    have : (shapeOf (Spec.HashTable.index w.l.G)).1 < R.kit.Q := by
      have h' : decide ((shapeOf (Spec.HashTable.index w.l.G)).1 < R.kit.Q) = true := h
      simpa using h'
    show (shapeOf _).1 ≤ _
    rcases R.hGD with e | ⟨e, -⟩ <;> omega
  hG8 := R.hG8
  hGQ := R.hGQ
  hsh := fun h => by
    have hs := shapeOf_ok (Spec.HashTable.index w.l.G)
    have : R.kit.Q ≤ (shapeOf (Spec.HashTable.index w.l.G)).1 := by
      have h' : decide ((shapeOf (Spec.HashTable.index w.l.G)).1 < R.kit.Q) = false := h
      simpa using h'
    rcases R.hsh with e | e
    · exact e
    · omega
  hshc := rfl
  hD16 := (shapeOf_ok _).1
  hD64 := (shapeOf_ok _).2.1
  hD4 := (shapeOf_ok _).2.2.1
  hS := by have := w.l.ok.hN; have := w.l.ok.hB64; show _ + _ ≤ 192; omega
  hct := rfl
  hT := hC.tries_pos
  hT' := hC.tries_lt
  hFN := rfl
  hcC := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.l.G w.l.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.l.len]

/-- The stack the code for any hash function uses. -/
theorem stack_le {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List TVar)
    (w : TVar) (hw : WOk w) : (rfcOf hC vs w hw).N ≤ stackT := by
  have hz := sizes (rfcOf hC vs w hw)
  have := hz.Q
  have := hz.H
  have := hz.X
  have h9 := (rfcOf hC vs w hw).kit.nw9
  have hnu : (rfcOf hC vs w hw).c.nums ≤ 2 := by rw [hz.nums]; split <;> omega
  have : (rfcOf hC vs w hw).c.frB ≤ 352 := by
    have e := hz.Q.2.2.2.1.2.2.1
    have : 8 * (rfcOf hC vs w hw).kit.nw ≤ 72 := by omega
    simp only [Cfg.frB] at e ⊢
    have : (rfcOf hC vs w hw).c.nw = (rfcOf hC vs w hw).kit.nw := rfl
    omega
  simp only [Rfc.N, stackT]
  omega

/-! ## The contract on entry -/

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (w : TVar) (s : State) : Prop :=
  (rfcRC R.kit.K (instOf T w) w.H (fnsOf vs) stackT).pre s ∧
    s.mem.readW (s.gpr .a5 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `a5` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.l.G w.l.ok.SH.H s.mem (s.gpr .a1) (s.gpr .a2)).1 with
    | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .a0) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .a0) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcRC R.kit.K (instOf T w) w.H (fnsOf vs) stackT).pub s₁ s₂

/-- The contract the proof is written against, for less stack. -/
theorem rfc_mono {K : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance}
    {H : Impl.Hmac.Stream.RISCV64.Hash} {f : Impl.RsaOaep.RISCV64.Fns} {N N' : Nat} {s : State} (hN : N' ≤ N)
    (h : (rfcRC K I H f N).pre s) : (rfcRC K I H f N').pre s := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25⟩, ⟨c1, c2, c3, c4⟩⟩ := h
  have hsub : Region.Sub (below (stripConsts K s).sp N') (below (stripConsts K s).sp N) :=
    below_sub hN (by simp only [stripConsts_sp] at h9 ⊢; omega)
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, by omega, h10.sub_left hsub, h11.sub_left hsub, h12.sub_left hsub,
    h13.sub_left hsub, h14, h15, h16, h17, h18, h19, h20, h21.sub_left hsub, h22, h23, h24, h25⟩,
    ⟨c1, c2, fun t ht => ⟨(c3 t ht).1, (c3 t ht).2.1, fun r hr => ?_⟩, c4⟩⟩
  have hres : ∀ {n : Nat}, r ∈ abi.reserved n s → r = below s.sp n := fun {n} hr' => by
    simp only [abi, stackBelow] at hr'
    split at hr' <;> simp_all
  obtain rfl := hres hr
  by_cases h0 : N' = 0
  · subst h0; simp [abi, stackBelow] at hr
  · exact (c3 t ht).2.2 _ (by
      show below s.sp N ∈ stackBelow s.sp N
      unfold stackBelow; split <;> first | omega | simp) |>.sub_right hsub

/-- The contract the proof is written against, of a state with the same
arguments, stack pointer, regions, memory and symbols. -/
theorem rfc_congr {K : List (String × List (BitVec 64))} {I : Spec.Ecdsa.Rfc6979.Instance}
    {H : Impl.Hmac.Stream.RISCV64.Hash} {f : Impl.RsaOaep.RISCV64.Fns} {N : Nat} {s t : State}
    (h : (rfcRC K I H f N).pre s) (hg : ∀ r ∈ [Reg.a0, .a1, .a2, .a4, .a5], t.gpr r = s.gpr r)
    (hsp : t.sp = s.sp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) :
    (rfcRC K I H f N).pre t := by
  have e₀ := hg .a0 (by simp); have e₁ := hg .a1 (by simp); have e₂ := hg .a2 (by simp)
  have e₄ := hg .a4 (by simp); have e₅ := hg .a5 (by simp)
  have ec : constRegs K t = constRegs K s := by simp only [constRegs, hsy]
  have er : abi.reserved N t = abi.reserved N s := by simp only [abi, hsp]
  have ws : ∀ (u : State) (a b : List Region), (u.withRegions a b).syms = u.syms := fun _ _ _ => rfl
  simp only [rfcRC, rfcR, ConstsOk, stripConsts, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.withRegions_mem, ws] at h ⊢
  rw [e₀, e₁, e₂, e₄, e₅, hsp, hrd, hwr, hm, hsy, ec, er]
  exact h

/-- Two hash functions whose tables have the same index are the same. -/
theorem same_hash {w w' : TVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.l.G) = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) :
    w'.l.G = w.l.G ∧ w'.l.ok.SH.H = w.l.ok.SH.H := by
  have e : Spec.HashTable.index w'.l.G = Spec.HashTable.index w.l.G := by
    have h₁ := hw.2.1; have h₂ := hw'.2.1
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG : w'.l.G = w.l.G := by
    have a := w.idx; have b := w'.idx
    rw [e, a] at b
    exact (Option.some.inj b).symm
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

theorem sub_beq_zero : ∀ i < 8, ∀ j < 8, (BitVec.ofNat 64 i - BitVec.ofNat 64 j == 0) = decide (i = j) := by
  decide

/-- `entry`: the table's index to `t2`. -/
theorem entry_ok {w : TVar} {s : State} (h : PreW R T vs w s) :
    WP isa (.block entry) s fun t => Upd s t .t2 (BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) ∧
      t.syms = s.syms := by
  obtain ⟨⟨⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h22, h23, -, -⟩, -⟩, hi⟩ := h
  simp only [stripConsts_gpr] at h22 h23
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .a5 + BitVec.ofNat 64 24) 8 := by
    refine ⟨⟨s.gpr .a5, 40⟩, List.mem_append_left _ ?_, Offset.contains_base _ (by omega) (by omega)⟩
    have : (stripConsts R.kit.K s).rd = s.rd.take (s.rd.length - R.kit.K.length) := rfl
    rw [this] at h1
    exact List.mem_of_mem_take (by rw [h1]; simp)
  unfold entry
  refine WP.of_syms (wp_ld (a := s.gpr .a5 + BitVec.ofNat 64 24) (by decide) rfl
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hin fun t u => WP.block_nil fun sy => ⟨?_, sy⟩)
  rwa [hi] at u

/-- `byIdx b is` runs `b i`, for the index `i` in `t2`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → (∀ j ∈ is, j < 8) → t.gpr .t2 = BitVec.ofNat 64 i →
    (∀ t', (∀ r, r ≠ .t3 → t'.gpr r = t.gpr r) → t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr →
      t'.sp = t.sp → t'.syms = t.syms → WP isa (b i) t' Q) →
    WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi List.not_mem_nil
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t (fun _ _ => rfl) rfl rfl rfl rfl rfl
  | j :: k :: is, i, t, hi, hlt, h2, h => by
    have hil := hlt i hi
    have hjl := hlt j (List.mem_cons_self ..)
    simp only [byIdx]
    refine WP.seq (WP.of_syms (wp_subi (imm := j) (by omega) fun t₁ u₁ => WP.block_nil fun sy => ?_))
    have hz : isa.eval (.zero .t3) t₁ = some (decide (i = j)) := by
      rw [VG.RISCV64.Steps.eval_zero, u₁.gpr, h2, sub_beq_zero i hil j hjl]
    refine WP.ite (M := isa) _ hz (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      subst hb
      exact h t₁ (fun r hr => u₁.other r hr) u₁.mem u₁.rd u₁.wr u₁.sp sy
    · rw [decide_eq_false_iff_not] at hb
      have hi' : i ∈ k :: is := (List.mem_cons.mp hi).resolve_left hb
      exact byIdx_wp hi' (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
        (by rw [u₁.other _ (by decide), h2])
        fun t'' hg hm hrd hwr hsp hsy => h t'' (fun r hr => (hg r hr).trans (u₁.other r hr)) (hm.trans u₁.mem)
          (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp) (hsy.trans sy)

theorem idx_mem {w : TVar} (hw : WOk w) : Spec.HashTable.index w.l.G ∈ idxs := by
  have := hw.2.1
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem idxs_lt : ∀ j ∈ idxs, j < 8 := by decide

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCode R T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCode signT
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨u, sy⟩ => ?_)
  refine byIdx_wp (idx_mem hw) idxs_lt u.gpr fun t' hg hm hrd hwr hsp hsy => ?_
  have hg' : ∀ r, r ≠ .t2 → r ≠ .t3 → t'.gpr r = s.gpr r := fun r h₂ h₃ => (hg r h₃).trans (u.other r h₂)
  have hpre : (rfcRC (rfcOf hC vs w hw).kit.K (rfcOf hC vs w hw).I (rfcOf hC vs w hw).H (rfcOf hC vs w hw).c.f
      (rfcOf hC vs w hw).N).pre t' :=
    rfc_mono (stack_le hC vs w hw) (rfc_congr hp.1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg' _ (by decide) (by decide))
      (hsp.trans u.sp) (hrd.trans u.rd) (hwr.trans u.wr) (hm.trans u.mem) (hsy.trans sy))
  show WP isa (rfcOf hC vs w hw).c.sign t' _
  refine WP.mono (correct hpre) fun s' ⟨⟨hcs, hsp', hra⟩, hpost⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [hcs r hr, hg' r (by revert r; decide) (by revert r; decide)]
  · rw [hsp', hsp, u.sp]
  · rw [hra, hg' _ (by decide) (by decide)]
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
    have e₁ := hg' .a1 (by decide) (by decide)
    have e₂ := hg' .a2 (by decide) (by decide)
    have e₀ := hg' .a0 (by decide) (by decide)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t'.mem (t'.gpr .a1) (t'.gpr .a2)).1 with
      | some rs => (s'.gpr .a0).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (t'.gpr .a0)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .a0).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (t'.gpr .a0)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, e₁, e₂, e₀, hm.trans u.mem] at hpost'
    exact hpost'

end VG.Proof.Ecdsa.Rfc6979.RISCV64
