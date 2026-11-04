module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.ByIdx
public import VerifiedGarbage.Proof.HashTable.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.ByIdx
meta import VerifiedGarbage.Proof.HashTable.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp

/-!
# Deterministic ECDSA on PPC64LE: the hash function of a table

`vg_ecdsa_<curve>_sign` (`signCode`) moves `scratch` to `r6`, loads the
index of the hash function from the table `hash` (its word 3) and runs the
code for that index's digest length and block size (`cfgT`), which calls the
table's functions. For the hash functions `vs` that pass the registration's
checks (`OK`: their functions of the same name have the same code, and each
is of one of the hash functions with HMAC, of the sizes its index's code is
for), the table of each `w` makes it the code for `w`'s hash function
(`rfcOf`), which meets the contract with that hash function fixed
(`sign_ok`, `sign_ct`). `tabK` states that contract for whichever of the
tables `hash` holds, on entry; `TableSpec.lean` shows
`TableInstance.signContract` implies it.

What the proof needs of the curve is `RfcCurve` (`Curve.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only wp_mov wp_ld)

/-- The code for the hash function of index `i`, on the curve `C`, with the
bound on candidates `tries` and the tables of `vs`. -/
def cfgT (C : RfcCurve) (tries : Nat) (vs : List TVar) (i : Nat) : Cfg :=
  ⟨(shapeOf i).1, (shapeOf i).2, fnsOf vs, C.R.E.curve.len, C.R.E.curve.n, tries, C.R.N, C.R.C⟩

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (C : RfcCurve) (tries : Nat) (vs : List TVar) : Prog isa :=
  signT s!"vg_ecdsa_{C.R.E.name}_sign" (cfgT C tries vs)

/-- The stack it uses: its frame's 48 bytes, and the most of any hash
function's code. -/
def stackT : Nat := 720

/-! ## The variants -/

/-- What the code needs of a hash function `w`: it has HMAC (over `w`'s block
size), its index is one of `hidx`, and that index's code is for `w`'s digest
length and block size; and the working space and states of `w`'s streaming
functions fit `scratch`'s. -/
def WOk (w : TVar) : Prop :=
  (match Spec.Ecdsa.Rfc6979.hmacOf w.l.G with
    | some F => F.blockSize = w.H.B
    | none => False) ∧
  Spec.HashTable.index w.l.G ∈ hidx ∧ shapeOf (Spec.HashTable.index w.l.G) = (w.H.D, w.H.B) ∧
  sWork + w.H.W ≤ sPad ∧ w.H.S ≤ 192

instance (w : TVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.Ecdsa.Rfc6979.hmacOf w.l.G <;> infer_instance

/-- What the registrations check of the hash functions whose tables the
function takes. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem labelHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.RsaOaep.PPC64LE.labelHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.RsaOaep.PPC64LE.labelHashes, List.mem_cons, List.not_mem_nil, or_false] at h
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

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (C : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = C.R.E
  tries_pos : 1 ≤ T.tries
  tries_lt : T.tries < 2 ^ 15

/-- The hash function's part of the proof. -/
def kitOf (vs : List TVar) (w : TVar) (hw : WOk w) : Kit :=
  ⟨w.H, w.l.ok, w.l.ct, fnsOf vs, hw.2.2.2.1, hw.2.2.2.2⟩

/-- The instance of the proof for the code of `w`'s index. -/
def rfcOf {C : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT C T) (vs : List TVar) (w : TVar)
    (hw : WOk w) : Rfc :=
  have hz : SizeOk C.R.E C.k (cfgT C T.tries vs (Spec.HashTable.index w.l.G)) :=
    (C.sizes _ hw.2.1).of rfl rfl rfl
  { K := kitOf vs w hw
    R := C.R
    c := cfgT C T.tries vs (Spec.HashTable.index w.l.G)
    I := instOf T w
    k := C.k
    hE := hC.ecdsa
    hHash := rfl
    hD := rfl
    hcD := by show (shapeOf _).1 = w.H.D; rw [hw.2.2.1]
    hcB := by show (shapeOf _).2 = w.H.B; rw [hw.2.2.1]
    hcf := rfl
    hcN := rfl
    hcC := rfl
    hcl := rfl
    hcn := rfl
    hct := rfl
    hk := hz.hk
    hk16 := hz.hk16
    hbits := hz.hbits
    hn₁ := hz.hn₁
    hn₂ := hz.hn₂
    hW := hz.hW
    hT := hC.tries_pos
    hT' := hC.tries_lt }

theorem hblkT (C : RfcCurve) (tries : Nat) (vs : List TVar) {i : Nat} (hi : i ∈ hidx) :
    HBlks (cfgT C tries vs i) := (hblk i hi).of rfl rfl

theorem cblkT (C : RfcCurve) (tries : Nat) (vs : List TVar) {i : Nat} (hi : i ∈ hidx) :
    CBlks (cfgT C tries vs i) := (C.cblk i hi).of rfl rfl rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.l.G w.l.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.l.len]

/-! ## The contract on entry -/

/-- The state on entry with `scratch` in `r6`, as `entry` leaves it. -/
def entryOf (s : State) : State := { s with gpr := fun r => if r = .r6 then s.gpr .r7 else s.gpr r }

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, of the state `entry` leaves, and the table's index. -/
def PreW (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (w : TVar) (s : State) : Prop :=
  (rfcPPC (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pre (entryOf s) ∧
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `r8` is. -/
def tabK (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW T vs w s →
    match (T.result w.l.G w.l.ok.SH.H s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW T vs w s₁ ∧ PreW T vs w s₂ ∧
    (rfcPPC (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pub (entryOf s₁) (entryOf s₂)

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, for less stack. -/
theorem rfc_mono {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {F : State → Prop} {ns : List String} {s : State}
    (hS : S' ≤ S) (h : (rfcPPC I S F ns).pre s) : (rfcPPC I S' F ns).pre s := by
  obtain ⟨hrd, hwr, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, nt, tout, tsc, tstk, hF⟩ := h
  have hsub : Region.Sub (below s.sp S') (below s.sp S) := Offset.sub_below _ hS (by omega)
  exact ⟨hrd, hwr, od, og, oc, dc, gc, ko.sub_left hsub, kd.sub_left hsub, kg.sub_left hsub, kc.sub_left hsub,
    no, nd, ng, nc, by omega, nt, tout, tsc, tstk.sub_left hsub, hF⟩

/-- The contract the proof is written against, of a state with the same
arguments, regions, memory and symbols. -/
theorem rfc_congr {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat} {G : Impl.Hmac.Stream.PPC64LE.Hash}
    {f : Impl.RsaOaep.PPC64LE.Fns} {ns : List String} {s t : State} (h : (rfcPPC I S (tabFacts G f) ns).pre s)
    (hg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r8], t.gpr r = s.gpr r) (hsp : t.sp = s.sp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : (rfcPPC I S (tabFacts G f) ns).pre t := by
  have e₁ := hg .r3 (by simp); have e₂ := hg .r4 (by simp); have e₃ := hg .r5 (by simp)
  have e₄ := hg .r6 (by simp); have e₅ := hg .r8 (by simp)
  simp only [rfcPPC, tabFacts] at h ⊢
  rw [e₁, e₂, e₃, e₄, e₅, hsp, hrd, hwr, hm, hsy]
  exact h

/-! ## Correctness -/

variable {C : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Proof.RsaOaep.PPC64LE.labelHashes)
    (hG' : G' ∈ Proof.RsaOaep.PPC64LE.labelHashes) (h : Spec.HashTable.index G = Spec.HashTable.index G') :
    G = G' := by
  simp only [Proof.RsaOaep.PPC64LE.labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)

theorem idx_lt {w : TVar} (hw : WOk w) : Spec.HashTable.index w.l.G < 8 := by
  have := hw.2.1
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

/-- Two hash functions whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : TVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.l.G) = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) :
    w'.l.G = w.l.G ∧ w'.l.ok.SH.H = w.l.ok.SH.H := by
  have e : Spec.HashTable.index w'.l.G = Spec.HashTable.index w.l.G := by
    have h₁ := idx_lt hw; have h₂ := idx_lt hw'
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG := index_inj w'.l.mem w.l.mem e
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `entry`'s effect, from the state on entry `σ`. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .r6 → r ≠ .r9 → u.gpr r = σ.gpr r) ∧ u.gpr .r6 = σ.gpr .r7 ∧
    u.gpr .r9 = σ.mem.readW (σ.gpr .r8 + BitVec.ofNat 64 24) 64 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧
    u.sp = σ.sp ∧ u.lr = σ.lr ∧ u.syms = σ.syms

/-- `entry`: `scratch` to `r6`, the table's index to `r9`. -/
theorem entry_ok {s : State} (ht : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 24) 8) :
    WP isa (.block entry) s (EntryF s) := by
  refine WP.of_syms (wp_mov (d := .r6) (n := .r7) fun t₁ o₁ e₁ => ?_)
  refine wp_ld (t := .r9) (n := .r8) (a := s.gpr .r8 + BitVec.ofNat 64 24) (by rw [o₁.gpr _ (by decide)])
    (by rw [o₁.rd, o₁.wr]; exact ht) (fun t₂ o₂ e₂ => wp_nil fun hsy => ⟨fun r h₆ h₉ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hsy⟩)
  · rw [o₂.gpr _ (by simpa using h₉), o₁.gpr _ (by simpa using h₆)]
  · rw [o₂.gpr _ (by decide), e₁]
  · rw [e₂, o₁.mem]
  · rw [o₂.mem, o₁.mem]
  · rw [o₂.rd, o₁.rd]
  · rw [o₂.wr, o₁.wr]
  · rw [o₂.sp, o₁.sp]
  · rw [o₂.lr, o₁.lr]

theorem idx_mem {w : TVar} (hw : WOk w) : Spec.HashTable.index w.l.G ∈ idxs := hidx_sub hw.2.1

/-- The frame of the hash function's code fits the stack below ours. -/
theorem stack_le (P : Rfc) : 400 + extra P.c.hHigh P.c.wide + 48 ≤ stackT := by
  unfold extra stackT; split
  · decide
  · split <;> decide

/-! ## The stack the code for a hash function's sizes uses -/

theorem sd_seq {a b : Prog isa} {n : Nat} (ha : sdepth a ≤ n) (hb : sdepth b ≤ n) : sdepth (.seq a b) ≤ n :=
  Nat.max_le.mpr ⟨ha, hb⟩

theorem sd_ite {c : Cond} {a b : Prog isa} {n : Nat} (ha : sdepth a ≤ n) (hb : sdepth b ≤ n) :
    sdepth (.ite c a b) ≤ n :=
  Nat.max_le.mpr ⟨ha, hb⟩

theorem sd_blk {is : List Instr} {n : Nat} : sdepth (.block is : Prog isa) ≤ n := Nat.zero_le n

theorem sd_icalls {i : Instr} {n : Nat} : ∀ {ts : List (String × Prog isa)}, (∀ q ∈ ts, sdepth q.2 ≤ n) →
    sdepth (Code.icalls i ts) ≤ n
  | [], _ => Nat.zero_le n
  | (nm, b) :: _, h => Nat.max_le.mpr ⟨h (nm, b) (List.mem_cons_self ..),
      sd_icalls fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- What bounds the stack the code uses: that of the functions the table's
calls may reach, and of `core`. -/
structure DOk (c : Cfg) : Prop where
  i : ∀ q ∈ c.f.init, sdepth q.2 ≤ 48
  u : ∀ q ∈ c.f.upd, sdepth q.2 ≤ 48
  f : ∀ q ∈ c.f.fin, sdepth q.2 ≤ 48
  core : sdepth c.coreC ≤ 96

theorem d_tcall {j : Nat} {ts : List (String × Prog isa)} (hts : ∀ q ∈ ts, sdepth q.2 ≤ 48) :
    sdepth (Cfg.tcall j ts) ≤ 48 := sd_seq sd_blk (sd_icalls hts)

section
variable {c : Cfg} (h : DOk c)
include h

theorem d_hmac (dA : List Instr) (len dst : Nat) : sdepth (c.hmac dA len dst) ≤ 48 :=
  sd_seq (sd_seq (sd_seq sd_blk (d_tcall h.i)) (sd_seq (sd_seq sd_blk (d_tcall h.i)) (sd_seq sd_blk
    (sd_seq (sd_seq sd_blk (d_tcall h.u)) (sd_seq sd_blk (sd_seq sd_blk (d_tcall h.u)))))))
    (sd_seq (sd_seq sd_blk (d_tcall h.u)) (sd_seq (sd_seq sd_blk (d_tcall h.f))
      (sd_seq (sd_seq sd_blk (d_tcall h.u)) (sd_seq (sd_seq sd_blk (d_tcall h.f)) sd_blk))))

theorem d_hmacV : sdepth c.hmacV ≤ 48 := d_hmac h _ _ _

theorem d_rekeyFull (b : Nat) : sdepth (c.rekeyFull b) ≤ 48 := sd_seq sd_blk (sd_seq (d_hmac h _ _ _) (d_hmacV h))

theorem d_rekey : sdepth c.rekey ≤ 48 := sd_seq sd_blk (sd_seq (d_hmac h _ _ _) (d_hmacV h))

omit h in
theorem d_conv (o s : Nat) : sdepth (c.conv o s) ≤ 48 := sd_seq sd_blk sd_blk

theorem d_candW : ∀ k, sdepth (c.candW k) ≤ 48
  | 0 => sd_blk
  | k + 1 => sd_seq (d_candW k) (sd_seq (d_hmacV h) sd_blk)

theorem d_cand : sdepth c.cand ≤ 48 := by
  unfold Cfg.cand Cfg.candTop
  split
  · refine sd_seq (d_candW h _) ?_
    split
    · exact sd_blk
    · exact d_conv _ _
  · exact d_hmacV h

omit h in
theorem d_start : sdepth c.start ≤ 48 := by
  unfold Cfg.start Cfg.xPrep
  split
  · refine sd_seq sd_blk (sd_seq ?_ sd_blk)
    split
    · exact sd_blk
    · exact sd_seq sd_blk (d_conv _ _)
  · exact sd_blk

theorem d_tryOne : sdepth c.tryOne ≤ 96 :=
  sd_seq ((d_cand h).trans (by decide)) (sd_seq sd_blk (sd_seq h.core (sd_seq sd_blk
    (sd_ite (sd_seq ((d_rekey h).trans (by decide)) sd_blk) sd_blk))))

theorem d_body : sdepth c.body ≤ 96 :=
  sd_seq sd_blk (sd_seq ((d_start (c := c)).trans (by decide)) (sd_seq ((d_rekeyFull h 0).trans (by decide))
    (sd_seq ((d_rekeyFull h 1).trans (by decide)) (sd_seq sd_blk (sd_seq (d_tryOne h) sd_blk)))))

theorem d_sign : sdepth c.sign ≤ 672 := by
  have hb := d_body h
  have he : extra c.hHigh c.wide ≤ 272 := by unfold extra; split <;> [decide; split <;> decide]
  simp only [Cfg.sign, sdepth, Instr.frameBytes, frameBytes]
  omega

end

theorem dOk_cfgT (C : RfcCurve) (tries : Nat) (vs : List TVar) (i : Nat) : DOk (cfgT C tries vs i) where
  i q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact (sdepth_le_fdepth _ w.l.ok.initPf).trans (by have := w.l.ok.initFd; omega)
  u q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact (sdepth_le_fdepth _ w.l.ok.updPf).trans (by have := w.l.ok.updFd; omega)
  f q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact (sdepth_le_fdepth _ w.l.ok.finPf).trans (by have := w.l.ok.finFd; omega)
  core := C.R.d

/-! ## In the frame -/

/-- The state the frame's body starts in. -/
abbrev inFrame (σ : State) : State := pushed .r0 (lrSaved σ)

/-- The frame's push changes only the 48 bytes below `sp`. -/
theorem inFrame_frame (σ : State) : Frame [below σ.sp 48] σ.mem (inFrame σ).mem :=
  ((Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      simpa [lrSaved] using below_contains σ.sp 0 0 (by decide) (by decide))).write (List.mem_singleton_self _) _
    (by simpa [lrSaved] using below_contains σ.sp 0 32 (by decide) (by decide))

/-- What `entry` and the comparisons leave, from the state on entry `σ`. -/
def InnerT (σ u : State) : Prop :=
  (∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r9 → r ≠ .r10 → u.gpr r = σ.gpr r) ∧ u.gpr .r6 = σ.gpr .r7 ∧
    u.mem = (inFrame σ).mem ∧ u.rd = σ.rd ∧ u.wr = (inFrame σ).wr ∧ u.sp = σ.sp - 48 ∧ u.syms = σ.syms

theorem innerT_of {σ t u : State} (he : EntryF (inFrame σ) t) (o : ∀ r, r ≠ .r10 → u.gpr r = t.gpr r)
    (hm : u.mem = t.mem) (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp) (hsy : u.syms = t.syms) :
    InnerT σ u :=
  ⟨fun r h₀ h₆ h₉ h₁₀ => by
      rw [o r h₁₀, he.1 r h₆ h₉]
      show (lrSaved σ).gpr r = _
      simp only [lrSaved, Proof.Mont.PPC64LE.write_gpr, h₀, ↓reduceIte],
    by rw [o _ (by decide), he.2.1]; show (lrSaved σ).gpr .r7 = _; simp [lrSaved, Proof.Mont.PPC64LE.write_gpr],
    hm.trans he.2.2.2.1, hrd.trans he.2.2.2.2.1, hwr.trans he.2.2.2.2.2.1, hsp.trans he.2.2.2.2.2.2.1,
    hsy.trans he.2.2.2.2.2.2.2.2⟩

theorem InnerT.only {σ u u' : State} (h : InnerT σ u) (o : Only [.r10] u u') (hsy : u'.syms = u.syms) :
    InnerT σ u' :=
  ⟨fun r h₀ h₆ h₉ h₁₀ => (o.gpr r (by simpa using h₁₀)).trans (h.1 r h₀ h₆ h₉ h₁₀), (o.gpr _ (by decide)).trans h.2.1,
    o.mem.trans h.2.2.1, o.rd.trans h.2.2.2.1, o.wr.trans h.2.2.2.2.1, o.sp.trans h.2.2.2.2.2.1,
    hsy.trans h.2.2.2.2.2.2⟩

/-- The regions of the call of the code for `w`'s sizes, from the arguments. -/
abbrev cRd (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (t : State) : List Region :=
  [⟨t.gpr .r4, T.ecdsa.curve.len⟩, ⟨t.gpr .r5, w.H.D⟩, ⟨t.gpr .r8, 40⟩]
abbrev cWr (T : Spec.Ecdsa.Rfc6979.TableInstance) (t : State) : List Region :=
  [⟨t.gpr .r3, 2 * T.ecdsa.curve.len⟩, ⟨t.gpr .r6, 8192⟩]

/-- The state that code starts in. -/
abbrev cE (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (t : State) : State :=
  t.callEntry.withRegions (cRd T w t) (cWr T t)

theorem cE_gpr (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (t : State) {r : Reg} (hr : r ∉ linkRegs) :
    (cE T w t).gpr r = t.gpr r := ce_gpr t _ _ hr

/-- An argument of the call, as on entry. -/
theorem inner_arg {w : TVar} {σ u : State} (h : InnerT σ u) :
    ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r8], (cE T w u).gpr r = (entryOf σ).gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [cE_gpr _ _ _ (by decide), h.1 _ (by decide) (by decide) (by decide) (by decide)]; simp [entryOf]
  · rw [cE_gpr _ _ _ (by decide), h.1 _ (by decide) (by decide) (by decide) (by decide)]; simp [entryOf]
  · rw [cE_gpr _ _ _ (by decide), h.1 _ (by decide) (by decide) (by decide) (by decide)]; simp [entryOf]
  · rw [cE_gpr _ _ _ (by decide), h.2.1]; simp [entryOf]
  · rw [cE_gpr _ _ _ (by decide), h.1 _ (by decide) (by decide) (by decide) (by decide)]; simp [entryOf]

/-- The contract the proof is written against, with the stack below a
frame of 48 bytes, of a state whose memory changed only there. -/
theorem rfc_shift {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {G : Impl.Hmac.Stream.PPC64LE.Hash}
    {f : Impl.RsaOaep.PPC64LE.Fns} {ns : List String} {s t : State} (h : (rfcPPC I S (tabFacts G f) ns).pre s)
    (hS : S' + 48 ≤ S) (hg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r8], t.gpr r = s.gpr r) (hsp : t.sp = s.sp - 48)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : Frame [below s.sp 48] s.mem t.mem) (hsy : t.syms = s.syms) :
    (rfcPPC I S' (tabFacts G f) ns).pre t := by
  have e₁ := hg .r3 (by simp); have e₂ := hg .r4 (by simp); have e₃ := hg .r5 (by simp)
  have e₄ := hg .r6 (by simp); have e₅ := hg .r8 (by simp)
  obtain ⟨hrd₀, hwr₀, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp₀, nt, tout, tsc, tstk,
    ⟨hok, hmem⟩⟩ := h
  have hsub : Region.Sub (below t.sp S') (below s.sp S) := fun a ha =>
    below_sub (sp := s.sp) (a := S' + 48) (b := S) hS (by omega) a
      (by rw [hsp] at ha; exact below_body s.sp S' a ha)
  have h48 : Region.Sub (below s.sp 48) (below s.sp S) := below_sub (by omega) (by omega)
  have htw : ∀ k < 3, t.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (8 * k)) 64 =
      s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (8 * k)) 64 := fun k hk =>
    hm.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * k), 8⟩) (w := 64)
      (by simpa only [Nat.reduceDiv] using Region.contains_self (s.gpr .r8 + BitVec.ofNat 64 (8 * k)) 8)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((tstk.sub_left h48).sub_right (Offset.sub_base _ (by omega))).symm) (by decide)
  refine ⟨by rw [hrd, hrd₀, e₂, e₃, e₅], by rw [hwr, hwr₀, e₁, e₄], by rw [e₁, e₂]; exact od, by rw [e₁, e₃]; exact og,
    by rw [e₁, e₄]; exact oc, by rw [e₂, e₄]; exact dc, by rw [e₃, e₄]; exact gc,
    by rw [e₁]; exact ko.sub_left hsub, by rw [e₂]; exact kd.sub_left hsub, by rw [e₃]; exact kg.sub_left hsub,
    by rw [e₄]; exact kc.sub_left hsub, by rw [e₁]; exact no, by rw [e₂]; exact nd, by rw [e₃]; exact ng,
    by rw [e₄]; exact nc, by rw [hsp, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 48 ≤ s.sp.toNat; omega)]; show S' ≤ s.sp.toNat - 48; omega, by rw [e₅]; exact nt,
    by rw [e₁, e₅]; exact tout, by rw [e₄, e₅]; exact tsc, by rw [e₅]; exact tstk.sub_left hsub,
    by rw [hsy]; exact hok, ?_⟩
  rw [hsy, e₅]
  obtain ⟨m₁, m₂, m₃⟩ := hmem
  refine ⟨?_, ?_, ?_⟩
  · have := htw 0 (by decide); rw [Nat.mul_zero, BitVec.add_zero] at this; rw [this]; exact m₁
  · have := htw 1 (by decide); rw [Nat.mul_one] at this; rw [this]; exact m₂
  · have := htw 2 (by decide); rw [show 8 * 2 = 16 from rfl] at this; rw [this]; exact m₃

/-- RFC 6979's result, from a memory that changed only below `sp`. -/
theorem result_frame {I : Spec.Ecdsa.Rfc6979.Instance} {sp : Addr} {m m' : Mem} (hm : Frame [below sp 48] m m')
    {d dg : Addr} (hd : (below sp 48).Disjoint ⟨d, I.ecdsa.curve.len⟩) (hg : (below sp 48).Disjoint ⟨dg, I.hashLen⟩)
    (hl : I.ecdsa.curve.len ≤ 2 ^ 64) (hl' : I.hashLen ≤ 2 ^ 64) :
    result I m' d dg = result I m d dg := by
  have e₁ : Spec.Ecdsa.bytesAt m' d I.ecdsa.curve.len = Spec.Ecdsa.bytesAt m d I.ecdsa.curve.len :=
    bytesAt_frame hm (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.symm) hl
  have e₂ : Spec.Ecdsa.bytesAt m' dg I.hashLen = Spec.Ecdsa.bytesAt m dg I.hashLen :=
    bytesAt_frame hm (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hg.symm) hl'
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result]
  rw [e₁, e₂]

/-! ## Correctness -/

theorem pre_sp {w : TVar} {σ : State} (hp : PreW T vs w σ) : 720 ≤ σ.sp.toNat := hp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The 48 bytes below `sp` are apart from the table, `d` and the digest. -/
theorem pre_apart {w : TVar} {σ : State} (hp : PreW T vs w σ) :
    (below σ.sp 48).Disjoint ⟨σ.gpr .r8, 40⟩ ∧ (below σ.sp 48).Disjoint ⟨σ.gpr .r4, T.ecdsa.curve.len⟩ ∧
      (below σ.sp 48).Disjoint ⟨σ.gpr .r5, w.H.D⟩ ∧ (below σ.sp 48).Disjoint ⟨σ.gpr .r3, 2 * T.ecdsa.curve.len⟩ ∧
      (below σ.sp 48).Disjoint ⟨σ.gpr .r7, 8192⟩ := by
  obtain ⟨⟨-, -, -, -, -, -, -, ko, kd, kg, kc, -, -, -, -, hsp, -, -, -, tstk, -⟩, -⟩ := hp
  have h48 : Region.Sub (below σ.sp 48) (below σ.sp stackT) := below_sub (by decide) (by decide)
  exact ⟨tstk.sub_left h48, kd.sub_left h48, kg.sub_left h48, ko.sub_left h48, kc.sub_left h48⟩

theorem inFrame_gpr (σ : State) {r : Reg} (hr : r ≠ .r0) : (inFrame σ).gpr r = σ.gpr r := by
  show (lrSaved σ).gpr r = _
  simp only [lrSaved, Proof.Mont.PPC64LE.write_gpr, hr, ↓reduceIte]

/-- The table's index, as on entry. -/
theorem inFrame_idx {w : TVar} {σ : State} (hp : PreW T vs w σ) :
    (inFrame σ).mem.readW ((inFrame σ).gpr .r8 + BitVec.ofNat 64 24) 64 =
      BitVec.ofNat 64 (Spec.HashTable.index w.l.G) := by
  rw [inFrame_gpr σ (by decide), ← hp.2]
  exact (inFrame_frame σ).readW (r := ⟨σ.gpr .r8 + BitVec.ofNat 64 24, 8⟩) (w := 64)
    (by simpa only [Nat.reduceDiv] using Region.contains_self (σ.gpr .r8 + BitVec.ofNat 64 24) 8)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((pre_apart hp).1.sub_right (Offset.sub_base _ (by decide))).symm) (by decide)

/-- `entry` may read the table's index. -/
theorem inFrame_in {w : TVar} {σ : State} (hp : PreW T vs w σ) :
    InRegions ((inFrame σ).rd ++ (inFrame σ).wr) ((inFrame σ).gpr .r8 + BitVec.ofNat 64 24) 8 := by
  have n8 := hp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨σ.gpr .r8, 40⟩, ?_, ?_⟩
  · show _ ∈ σ.rd ++ _
    rw [show σ.rd = (entryOf σ).rd from rfl, hp.1.1]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · rw [inFrame_gpr σ (by decide)]
    exact Offset.contains_base _ (by decide) (by have : (entryOf σ).gpr .r8 = σ.gpr .r8 := rfl; omega)

/-- In the frame, the contract with `w`'s hash function fixed holds of the
call's entry, whose regions the frame's body may access. -/
theorem inner_pre (hC : CurveT C T) {w : TVar} (hw : WOk w) {σ u : State} (hp : PreW T vs w σ) (hi : InnerT σ u) :
    (rfcP (rfcOf hC vs w hw) (names vs)).pre (cE T w u) ∧ Covers (cRd T w u ++ cWr T u) (u.rd ++ u.wr) ∧
      Covers (cWr T u) u.wr := by
  have g := inner_arg (T := T) (w := w) hi
  have g3 := g .r3 (by simp); have g4 := g .r4 (by simp); have g5 := g .r5 (by simp)
  have g6 := g .r6 (by simp); have g8 := g .r8 (by simp)
  rw [cE_gpr _ _ _ (by decide)] at g3 g4 g5 g6 g8
  have hrd : cRd T w u = σ.rd := by
    rw [show σ.rd = (entryOf σ).rd from rfl, hp.1.1, ← g4, ← g5, ← g8]; rfl
  have hwr : cWr T u = σ.wr := by
    rw [show σ.wr = (entryOf σ).wr from rfl, hp.1.2.1, ← g3, ← g6]; rfl
  refine ⟨rfc_shift hp.1 (stack_le _) g (by simp only [State.withRegions_sp, State.callEntry_sp]; exact hi.2.2.2.2.2.1)
    (by simp only [State.withRegions_rd]; exact hrd)
    (by simp only [State.withRegions_wr]; exact hwr) (by
      show Frame _ σ.mem u.mem
      rw [hi.2.2.1]; exact inFrame_frame σ) hi.2.2.2.2.2.2, ?_, ?_⟩
  · rw [hrd, hwr, hi.2.2.2.1, hi.2.2.2.2.1]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_append] at hr ⊢; tauto
  · rw [hwr, hi.2.2.2.2.1]
    exact Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr

/-- RFC 6979's result for the call's arguments, as on entry. -/
theorem inner_result {w : TVar} {σ u : State} (hp : PreW T vs w σ) (hi : InnerT σ u) :
    result (instOf T w) (cE T w u).mem ((cE T w u).gpr .r4) ((cE T w u).gpr .r5) =
      result (instOf T w) σ.mem (σ.gpr .r4) (σ.gpr .r5) := by
  have g := inner_arg (T := T) (w := w) hi
  rw [g .r4 (by simp), g .r5 (by simp)]
  show result (instOf T w) u.mem _ _ = _
  rw [hi.2.2.1]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, nd, ng, -⟩ := hp.1
  exact result_frame (inFrame_frame σ) (pre_apart hp).2.1 (pre_apart hp).2.2.1 (by omega) (by omega)

/-- The return address the frame saved is kept by the call, which writes
only its buffers and the stack below the frame. -/
theorem lr_kept {w : TVar} {σ u : State} (hp : PreW T vs w σ) (hi : InnerT σ u) {m : Mem} {d : Nat} (hd : d ≤ 672)
    (hf : Frame (cWr T u ++ [below u.sp d]) u.mem m) : m.read (u.sp + 32) 8 = σ.lr := by
  have hsp := pre_sp hp
  have hsu := hi.2.2.2.2.2.1
  have hc : Region.Sub ⟨σ.sp - 48 + 32, 8⟩ (below σ.sp 48) := fun a ha => by
    have := below_contains σ.sp 0 32 (by decide) (by decide); simp only [Region.Contains] at ha this ⊢; bv_omega
  rw [Frame.read hf (r := ⟨u.sp + 32, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), read8, hi.2.2.1, hsu]
  · show ((σ.mem.writeW (σ.sp - 48) σ.sp).writeW (σ.sp - 48 + 32) σ.lr).readW (σ.sp - 48 + 32) 64 = σ.lr
    exact Mem.readW_writeW_self64 _ _ _
  · rw [hsu]
    have g := inner_arg (T := T) (w := w) hi
    have g3 := g .r3 (by simp); have g6 := g .r6 (by simp)
    rw [cE_gpr _ _ _ (by decide)] at g3 g6
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · rw [g3]; exact ((pre_apart hp).2.2.2.1.sub_left hc)
    · rw [g6]; exact ((pre_apart hp).2.2.2.2.sub_left hc)
    · intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      bv_omega

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers, the stack pointer and the return address. -/
theorem signT_ok (hC : CurveT C T) {σ : State} (h : (tabK T vs).pre σ) :
    WP isa (signCode C T.tries vs) σ fun s' => abiPreserved σ s' ∧ (tabK T vs).post σ s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  have hsp := pre_sp hp
  unfold signCode signT
  refine WP.seq (Proof.Mont.PPC64LE.wp_step exec_mflr (wp_nil ?_))
  refine WP.seq (WP.frame (show 48 ≤ σ.sp.toNat by omega) ?_)
  refine WP.seq (WP.mono (entry_ok (inFrame_in hp)) fun t he => ?_)
  refine byIdx_ok (b := fun i => .call (shapeName s!"vg_ecdsa_{C.R.E.name}_sign" (cfgT C T.tries vs i))
      (cfgT C T.tries vs i).sign) (D := Spec.HashTable.index w.l.G) (by have := idx_lt hw; omega)
    (F := fun u => InnerT σ u ∧ u.gpr .r9 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G))
    (fun u hu => hu.2) (fun u u' ⟨hu, h9⟩ o hsy => ⟨hu.only o hsy, (o.gpr _ (by decide)).trans h9⟩)
    (fun u ⟨hu, _⟩ => ?_) (idx_mem hw) (fun x hx => (idxs_certs x hx).1) t
    ⟨innerT_of he (fun _ _ => rfl) rfl rfl rfl rfl rfl, he.2.2.1.trans (inFrame_idx hp)⟩
  obtain ⟨hpre, hcov, hcovw⟩ := inner_pre hC hw hp hu
  have hd := d_sign (dOk_cfgT C T.tries vs (Spec.HashTable.index w.l.G))
  refine WP.callAny (k := rfcP (rfcOf hC vs w hw) (names vs)) (fun s h => sign_ok h) hpre hcov hcovw
    (fun s' hrd hwr hsp' hf hcs hpost => ?_) (Nat.lt_of_le_of_lt hd (by decide))
  refine Proof.Mont.PPC64LE.wp_step exec_mtlr (wp_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩)
  · have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    show (s'.write .r0 _).gpr r = _
    rw [Proof.Mont.PPC64LE.write_gpr]; simp only [h0, ↓reduceIte]
    rw [hcs r hr, hu.1 r h0 (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))]
  · show s'.sp + 48 = σ.sp
    rw [hsp', hu.2.2.2.2.2.1, BitVec.sub_add_cancel]
  · show (s'.write .r0 (s'.mem.read (s'.sp + 32) 8)).gpr .r0 = σ.lr
    rw [Proof.Mont.PPC64LE.write_gpr]; simp only [↓reduceIte]
    rw [hsp']
    exact lr_kept hp hu (d := sdepth (cfgT C T.tries vs (Spec.HashTable.index w.l.G)).sign) hd hf
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
    have g3 := inner_arg (T := T) (w := w) hu .r3 (by simp)
    rw [cE_gpr _ _ _ (by decide)] at g3
    rw [hG, hH]
    have hpost' : match (result (instOf T w) (cE T w u).mem ((cE T w u).gpr .r4) ((cE T w u).gpr .r5)).1 with
      | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem ((cE T w u).gpr .r3)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .r3).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem ((cE T w u).gpr .r3)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [inner_result hp hu, cE_gpr _ _ _ (by decide), g3, show (entryOf σ).gpr .r3 = σ.gpr .r3 from rfl] at hpost'
    simp only [result, tresult_eq] at hpost'
    have e3 : (s'.write .r0 (s'.mem.read (s'.sp + 32) 8)).gpr .r3 = s'.gpr .r3 := by
      rw [Proof.Mont.PPC64LE.write_gpr]; simp
    show match (T.result w.l.G w.l.ok.SH.H σ.mem (σ.gpr .r4) (σ.gpr .r5)).1 with
      | some rs => ((s'.write .r0 (s'.mem.read (s'.sp + 32) 8)).gpr .r3).setWidth 32 = 1 ∧
          Spec.Ecdsa.bytesAt s'.mem (σ.gpr .r3) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => ((s'.write .r0 (s'.mem.read (s'.sp + 32) 8)).gpr .r3).setWidth 32 = 0 ∧
          Spec.Ecdsa.bytesAt s'.mem (σ.gpr .r3) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
    rw [e3]
    exact hpost'

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
