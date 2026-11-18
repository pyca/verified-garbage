module

meta import VerifiedGarbage.Proof.MlKem.X86_64.Enc16
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkBase
public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16
meta import VerifiedGarbage.Impl.MlKem.X86_64.Encaps16
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkScalar
public import VerifiedGarbage.Proof.MlKem.X86_64.KgA
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgA
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlKem.X86_64.Zero
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkBase
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Spec.MlKem
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
public import VerifiedGarbage.Proof.MlKem.X86_64.FragS4_16
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps
public import VerifiedGarbage.Proof.MlKem.X86_64.KgBase
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragS4_16
meta import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
meta import VerifiedGarbage.Impl.MlKem.X86_64.Encaps
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgBase

/-! ### `MlKem.X86_64.EkInline16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: a fragment `Sample4.sampleH` with 16-bit coefficients, inlined

As `EkInline.lean`, for a fragment meeting `sampleHKW true` (`BatchHOk16`):
the polynomials from `sc oa` are of 16-bit coefficients, 512 bytes each
(`SHH16`, `sampleHAt16_ok`, `sampleHAt16_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

/-- What inlining the fragment needs: `S4H`, and the return address apart. -/
structure SHH16 (oa oz : Nat) (s : State) : Prop extends S4H16 oa oz s where
  rS : (retR s).Disjoint ⟨pa s (sc 0), 136⟩
  rA : (retR s).Disjoint ⟨pa s (sc oa), 2048⟩
  rZ : (retR s).Disjoint ⟨pa s (sc oz), 8192⟩

theorem SHH16.of {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {oa oz : Nat}
    (hc : s4_16Chk (rbs ++ wbs) wbs oa oz = true) : SHH16 oa oz s := by
  have h := S4H16.of L hc
  simp only [s4_16Chk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨_, hra⟩, _⟩, ⟨_, hrz⟩, _⟩, _⟩, _⟩, _⟩ := hc
  have ret : ∀ {p : Ptr} {l : Nat}, inB (rbs ++ wbs) p l = true → (retR s).Disjoint ⟨pa s p, l⟩ := fun hp => by
    obtain ⟨n, hn, hsub⟩ := L.sub hp
    exact (L.ret _ hn).sub_right hsub
  exact ⟨h, ret hrs, ret hra, ret hrz⟩

/-- The fragment's precondition, on its permissions. -/
theorem shPre16 {oa oz : Nat} {s s1 : State} (h : SHH16 oa oz s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz))
    (k : Keep argRegs s s1) :
    (sampleHKW true).pre (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have rr : ∀ rd wr, retR (s1.withRegions rd wr) = retR s := fun _ _ => by
    simp only [retR, State.withRegions_gpr, hsp]
  have b24 : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 24).Disjoint R :=
    fun hd => by rw [hsp]; exact hd.sub_left (below_sub (by omega_using []) (by omega_using []))
  simp only [sampleHKW, sample4KW, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, hv.1, hv.2.1,
    hv.2.2]
  exact ⟨trivial, rfl, h.dSA, h.dSZ, h.dAZ, by rw [rr]; exact h.rS, by rw [rr]; exact h.rA,
    by rw [rr]; exact h.rZ, b24 h.kS, b24 h.kA, b24 h.kZ, h.nwA, h.nwZ⟩

/-- Whether `SampleNTT` of the first three seeds at `p` all succeed within 280 iterations. -/
abbrev all3_16 (m : Mem) (p : Addr) : Bool :=
  (List.range 3).all fun k => (sampleNTT minIterations (seed4 m p k)).isSome

/-- What the fragment leaves. -/
structure SHPost16 (oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all3_16 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIsW 16 s'.mem (poly4W true (pa s (sc oa)) k) f
  hs : stateAt s'.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS) =
    SH.habs (stateAt s.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS))
      (fun i => bytesAt s.mem (pa s (sc oz) + BitVec.ofNat 64 (Sample4.oHB + 136 * i)) 136) 3

theorem SHPost16.b {oa oz : Nat} {s s' : State} (h : SHPost16 oa oz s s') :
    PPostB s s' [(sc oa, 2048), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

/-- The fragment inlined, on the seeds at `scratch`, to the polynomials from `sc oa`. -/
theorem sampleHAt16_ok {b : Prog isa} (hb : BatchHOk16 b) {oa oz : Nat} {s : State} (h : SHH16 oa oz s) :
    WP isa (Encaps.sampleHAt b (sc oa) (sc oz)) s (SHPost16 oa oz s) := by
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hc : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) (s1.rd ++ s1.wr) := by
    rw [k.2.1, k.2.2]; exact h.c
  have hw : Covers [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.wr := by rw [k.2.2]; exact h.w
  refine WP.seq (WP.mono (WP.inline hb.ok (shPre16 h hv k) hc hw (Q := fun s2 => s2.rd = s1.rd ∧ s2.wr = s1.wr ∧
      abiPreserved s1 s2 ∧ Frame [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.mem s2.mem ∧
      (sampleHKW true).post (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩])
        (s2.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]))
    (fun s2 hrd hwr habi hf _ hpost => ⟨hrd, hwr, habi, hf, hpost⟩) hb.noCalls) fun s2 ⟨hrd, hwr, habi, hf, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [sampleHKW, State.withRegions_gpr, State.withRegions_mem, hv.1, hv.2.1, hv.2.2, hm] at hpost
  obtain ⟨hax, hres, hhs⟩ := hpost
  have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := habi.1
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm]
    exact hf.mono fun r hr => List.mem_append_left _ hr
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hax]
  · rw [hm3]; exact hres j hj f hf
  · rw [hm3]; exact hhs

/-- Two runs of the fragment inlined, from the same seeds and pointers. -/
theorem sampleHAt16_tr {b : Prog isa} (hb : BatchHOk16 b) {oa oz : Nat} :
    RelCT isa (fun x y => SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136)
      (Encaps.sampleHAt b (sc oa) (sc oz)) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = pa x (sc oa) ∧ x1.gpr .rdx = pa x (sc oz)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = pa y (sc oa) ∧ y1.gpr .rdx = pa y (sc oz)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨s4Glue_ok oa oz hx.offA hx.offZ x, s4Glue_ok oa oz hy.offA hy.offZ y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (regionModel.relCT_inline (Pre := (sampleHKW true).pre)
      (Pub := (sampleHKW true).pub) (fun s hs => let ⟨t, s', e, _, p⟩ := hb.ok s hs; ⟨t, s', e, p⟩) hb.ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, shPre16 hx hv1 k1, shPre16 hy hv2 k2, ?_,
    by show Covers _ (x1.rd ++ x1.wr); rw [k1.2.1, k1.2.2]; exact hx.c,
    by show Covers _ x1.wr; rw [k1.2.2]; exact hx.w,
    by show Covers _ (y1.rd ++ y1.wr); rw [k2.2.1, k2.2.2]; exact hy.c,
    by show Covers _ y1.wr; rw [k2.2.2]; exact hy.w⟩
  show sample4K.pub (x1.withRegions _ _) (y1.withRegions _ _)
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1,
    hv2.2.2, hm1, hm2, e4, hs1, hs2, e3]
  simp only [pa, e1, and_self]

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.EkFrag`, which this module and modules that import it used -/

section

/-! ### `MlKem.HSponge`, which this module and modules that import it used -/

section

/-!
# `H(ek)` absorbed one block at a time

`hstate E b d`: the state of the sponge of rate 136 and suffix `d` (SHA3-256's
`0x06` by default, SHAKE256's `0x1f`) before
block `b` of `pad(E)` is absorbed: the sponge of the first `b` blocks of
`E`, and, once every block is absorbed, `absorb 136 (pad 136 6 E)`, the state
`H(E)` is squeezed from (`H_of_hstate`). A whole block of `E` takes
`hstate E b` to `hstate E (b + 1)` (`hstate_full`), and so does the last,
partial block, followed by the padding (`hstate_last`, `hstate_padBlock`:
the padding as bytes of the block, `E`'s rest, `0x06`, zeros and `0x80`).

(AArch64's encapsulation absorbs `ek` in the same way, in
`Proof/MlKem/AArch64/Hybrid/Absorb.lean`.)
-/

@[expose] public section

namespace VG.Proof.MlKem.HSponge

open VG.Spec.Sha3 (State keccakF absorb pad stateAt bytesAt toBytes)
open VG.Proof.Sha3 (Rep xorAt xorByte byteOf)

/-- The state before block `b` of `pad(E)` is absorbed. -/
def hstate (E : List Byte) (b : Nat) (d : Byte := BitVec.ofNat 8 6) : State :=
  if 136 * b ≤ E.length then Rep 136 (E.take (136 * b)) else absorb 136 (pad 136 d E)

theorem hstate_zero (E : List Byte) {d : Byte} : hstate E 0 d = Spec.Sha3.zero := by
  simp only [hstate, Nat.mul_zero, Nat.zero_le, ite_true, List.take_zero, Proof.Sha3.rep_nil]

theorem hstate_done {E : List Byte} {b : Nat} {d : Byte} (h : E.length < 136 * b) :
    hstate E b d = absorb 136 (pad 136 d E) := by
  simp only [hstate, ite_eq_right (show ¬136 * b ≤ E.length by omega_using [h])]

theorem xorAt_nil (A : State) (j : Nat) : xorAt A j [] = A := rfl

theorem xorAt_append (A : State) (j : Nat) (bs : List Byte) :
    ∀ cs, xorAt A j (bs ++ cs) = xorAt (xorAt A j bs) (j + bs.length) cs := by
  refine Proof.Sha3.snoc_induction ?_ ?_
  · rw [List.append_nil]; exact (xorAt_nil _ _).symm
  · intro cs c ih
    rw [← List.append_assoc, Proof.Sha3.xorAt_snoc, ih, Proof.Sha3.xorAt_snoc, List.length_append,
      Nat.add_assoc]

theorem xorAt_zeros (A : State) (j : Nat) : ∀ n, xorAt A j (List.replicate n 0) = A
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ', Proof.Sha3.xorAt_snoc, xorAt_zeros A j n]
    refine Proof.Sha3.ext_bytes fun i hi => ?_
    rw [Proof.Sha3.byteOf_xorByte _ _ _ hi]
    split <;> simp

/-- A whole block. -/
theorem hstate_full {E : List Byte} {b : Nat} {d : Byte} (h : 136 * b + 136 ≤ E.length) :
    keccakF (xorAt (hstate E b d) 0 ((E.drop (136 * b)).take 136)) = hstate E (b + 1) d := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega_using [h])
  have hbs : ((E.drop (136 * b)).take 136).length = 136 := by
    rw [List.length_take, List.length_drop]; omega_using [h]
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    ((E.drop (136 * b)).take 136) (by omega_using [hbs]) (by rw [hl, hbs]; omega_using [])
  rw [hl, hbs, show 136 * b % 136 = 0 by omega_using [], ite_eq_left (by decide)] at ra
  have ht : E.take (136 * (b + 1)) = E.take (136 * b) ++ (E.drop (136 * b)).take 136 := by
    rw [show 136 * (b + 1) = 136 * b + 136 by omega_using [], List.take_add]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega_using [h]),
    ite_eq_left (show 136 * (b + 1) ≤ E.length by omega_using [h]), ht, ra]

/-- The last, partial block, and the padding. -/
theorem hstate_last {E : List Byte} {b : Nat} {d : Byte} (hlo : 136 * b < E.length)
    (hhi : E.length < 136 * b + 136) :
    keccakF (xorByte (xorByte (xorAt (hstate E b d) 0 (E.drop (136 * b))) (E.length - 136 * b) d) 135 128) =
      hstate E (b + 1) d := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega_using [hlo])
  have hbs : (E.drop (136 * b)).length = E.length - 136 * b := List.length_drop
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    (E.drop (136 * b)) (by omega_using [hlo, hbs]) (by rw [hl, hbs]; omega_using [hhi])
  rw [hl, hbs, show 136 * b % 136 = 0 by omega_using [], ite_eq_right (show ¬0 + (E.length - 136 * b) = 136 by omega_using [hhi]),
    List.take_append_drop] at ra
  rw [hstate_done (show E.length < 136 * (b + 1) by omega_using [hhi]),
    Proof.Sha3.absorb_pad (by decide) (by decide), show E.length % 136 = E.length - 136 * b by omega_using [hlo, hhi]]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega_using [hlo]), ← ra]

/-- The last block of `pad(E)`, of 136 bytes: `E`'s rest `X`, the suffix `d` (`0x06` by default), zeros,
and `0x80`. -/
def padBlock (X : List Byte) (d : Byte := BitVec.ofNat 8 6) : List Byte :=
  X ++ [d] ++ List.replicate (134 - X.length) 0 ++ [BitVec.ofNat 8 0x80]

theorem xorAt_padBlock (A : State) {X : List Byte} {d : Byte} (h : X.length ≤ 134) :
    xorAt A 0 (padBlock X d) = xorByte (xorByte (xorAt A 0 X) X.length d) 135 128 := by
  rw [padBlock, xorAt_append, xorAt_append, xorAt_append, xorAt_zeros, Proof.Sha3.xorAt_single,
    Proof.Sha3.xorAt_single]
  simp only [Nat.zero_add, List.length_append, List.length_singleton, List.length_replicate,
    show X.length + 1 + (134 - X.length) = 135 by omega_using [h]]
  rfl

/-- The last, partial block, as bytes of the padded block. -/
theorem hstate_padBlock {E : List Byte} {b : Nat} {d : Byte} (hlo : 136 * b < E.length)
    (hhi : E.length < 136 * b + 135) :
    keccakF (xorAt (hstate E b d) 0 (padBlock (E.drop (136 * b)) d)) = hstate E (b + 1) d := by
  rw [xorAt_padBlock _ (by rw [List.length_drop]; omega_using [hhi]), List.length_drop]
  exact hstate_last hlo (by omega_using [hhi])

/-- `H(E)`, from the state after the last block. -/
theorem H_of_hstate {E : List Byte} {b : Nat} (h : E.length < 136 * b) :
    Spec.MlKem.H E = (toBytes (hstate E b)).take 32 := by
  rw [hstate_done h]
  show (List.take 32 ((toBytes _).take 136 ++ [])) = _
  rw [List.append_nil, List.take_take]
  rfl

/-- `J(E)`, from the state (suffix `0x1f`) after the last block. -/
theorem J_of_hstate {E : List Byte} {b : Nat} (h : E.length < 136 * b) :
    Spec.MlKem.J E = (toBytes (hstate E b (BitVec.ofNat 8 0x1f))).take 32 := by
  rw [hstate_done h]
  show (List.take 32 ((toBytes _).take 136 ++ [])) = _
  rw [List.append_nil, List.take_take]
  rfl

/-- The first 32 bytes of a state in memory. -/
theorem bytesAt_stateAt (m : Mem) (p : Addr) : bytesAt m p 32 = (toBytes (stateAt m p)).take 32 := by
  refine List.ext_getElem (by simp [bytesAt, Proof.Sha3.length_toBytes]) fun i h₁ h₂ => ?_
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  rw [List.getElem_take, Proof.Sha3.toBytes_getElem _ (by omega_using [h₁]), Proof.Sha3.byteOf_stateAt _ _ (by omega_using [h₁])]
  simp [bytesAt]

end VG.Proof.MlKem.HSponge

end

end

/-!
# ML-KEM on x86-64: encapsulation hashing the key in the matrix's fragments, what does not depend on the layout

The facts about `pad(ek)` and its blocks (`blk`, `hbE`), the sponge's state
after them (`hstate_blk`, `habs_blk`), and the pieces of code
(`zeros_ok`, `mov0_ok`) that `kemEncaps16`'s fragments use
(`EkFrag16.lean`), whatever the layout.
-/

@[expose] public section
namespace VG.Proof.MlKem.X86_64.EkF

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.Sha3 (xorAt)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs)
open VG.Proof.MlKem.HSponge (hstate padBlock)

/-! ## The blocks of `pad(ek)` -/

/-- Block `t` of `pad(E)` (suffix `d`, `0x06` by default), for `E` that does not end at a block boundary. -/
def blk (E : List Byte) (t : Nat) (d : Byte := BitVec.ofNat 8 6) : List Byte :=
  if 136 * t + 136 ≤ E.length then (E.drop (136 * t)).take 136 else padBlock (E.drop (136 * t)) d

/-- `E`'s length leaves a partial last block, with room for the padding. -/
def Partial (E : List Byte) : Prop := 0 < E.length % 136 ∧ E.length % 136 < 135

theorem hstate_blk {E : List Byte} {d : Byte} (hE : Partial E) {t : Nat} (ht : t ≤ E.length / 136) :
    keccakF (xorAt (hstate E t d) 0 (blk E t d)) = hstate E (t + 1) d := by
  unfold blk
  split
  · exact HSponge.hstate_full (by omega_arith)
  · have := Nat.div_add_mod E.length 136
    exact HSponge.hstate_padBlock (by obtain ⟨h1, h2⟩ := hE; omega_using [ht, h1]) (by obtain ⟨h1, h2⟩ := hE; omega_arith)

theorem habs_blk {E : List Byte} {d : Byte} (hE : Partial E) {i : Nat} (hi : 3 * i + 3 ≤ E.length / 136 + 1) :
    SH.habs (hstate E (3 * i) d) (fun j => blk E (3 * i + j) d) 3 = hstate E (3 * i + 3) d := by
  simp only [SH.habs, Nat.add_zero]
  rw [hstate_blk hE (by omega_using [hi]), hstate_blk hE (by omega_using [hi]), hstate_blk hE (by omega_using [hi])]

/-! ## The sponge's state -/

theorem stateAt_keep {rbs wbs : List (Reg × Nat)} {s s' : State} (Lx : Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) {p : Ptr} (hc : keepB (rbs ++ wbs) ws p 200 = true) :
    stateAt s'.mem (pa s' p) = stateAt s.mem (pa s p) := by
  have e := Lx.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at e ⊢
  refine VG.Proof.Sha3.stateAt_congr fun i hi => ?_
  have := congrArg (fun l => l[i]?) e
  simpa [bytesAt, List.getElem?_map, List.getElem?_range hi] using this

/-! ## Zeros and the padding -/


theorem zeros_ok (b : Reg) (off n : Nat) (s : State) (h0 : s.gpr .rax = 0) (hn : 8 * n < 2 ^ 64)
    (hw : ∀ j < n, InRegions s.wr (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.block ((List.range n).flatMap fun j => [.store (at_ b (off + 8 * j)) .rax])) s fun s' =>
      Keep [] s s' ∧ Frame [⟨s.gpr b + BitVec.ofNat 64 off, 8 * n⟩] s.mem s'.mem ∧
        ∀ i < 8 * n, s'.mem (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = 0 := by
  refine wp_range_flatMap (M := isa) (fun k s' => Keep [] s s' ∧
      Frame [⟨s.gpr b + BitVec.ofNat 64 off, 8 * n⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = 0)
    (fun k s' hk ⟨hk', hf, hz⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hb : s'.gpr b = s.gpr b := hk'.1 b (by simp)
  have ha : s'.gpr .rax = 0 := by rw [hk'.1 .rax (by simp), h0]
  have e : s.gpr b + BitVec.ofNat 64 (off + 8 * k) = s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine WP.mono (zeroStep_ok b (off + 8 * k) s' (by rw [hk'.2.2, hb, e]; exact hw k hk))
    fun s'' ⟨hm, hk''⟩ => ⟨(hk'.trans hk'').mono (by simp), ?_, fun i hi => ?_⟩
  · rw [hm, hb, e]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hn, hk]))
  · rw [hm, hb, e, ha]
    simp only [Mem.writeW, Mem.write]
    split
    · simp
    · rename_i hc
      refine hz i (Nat.lt_of_not_le fun hik => hc ?_)
      rw [Offset.sub_toNat _ hik (by omega_using [hn, hk, hi])]
      omega_using [hi]

theorem mov0_ok (s : State) :
    WP isa (.block [.mov32 .rax (.imm 0)]) s fun s' => s'.gpr .rax = 0 ∧ s'.mem = s.mem ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.gpr .rax = 0 ∧ s'.mem = s.mem) ?_ (by rfl))
    fun s' ⟨⟨h0, hm⟩, k⟩ => ⟨h0, hm, k⟩
  xrun []

theorem padList (n : Nat) (a b : Byte) :
    ((List.replicate (n + 2) (0 : Byte)).set 0 a).set (n + 1) b = a :: (List.replicate n 0 ++ [b]) := by
  rw [List.replicate_succ, List.set_cons_zero, List.set_cons_succ, List.replicate_succ', List.set_append_right _ _ (by simp),
    List.length_replicate, Nat.sub_self, List.set_cons_zero]

/-! ## The blocks of a fragment -/

/-- The 408 bytes of `pad(E)` (suffix `d`) from `408 i`, for `E` whose last block ends in fragment `i` or later. -/

def hbE (E : List Byte) (i : Nat) (d : Byte := BitVec.ofNat 8 6) : List Byte :=
  if 408 * i + 408 ≤ E.length then (E.drop (408 * i)).take 408
  else E.drop (408 * i) ++ d :: (List.replicate (406 - (E.length - 408 * i)) 0 ++ [BitVec.ofNat 8 0x80])

theorem hbE_blk {E : List Byte} {d : Byte} {i j : Nat} (hj : j < 3)
    (hp : 408 * i + 408 ≤ E.length ∨ (272 < E.length - 408 * i ∧ E.length - 408 * i < 406)) :
    ((hbE E i d).drop (136 * j)).take 136 = blk E (3 * i + j) d := by
  unfold hbE blk
  split
  · rw [ite_eq_left (show 136 * (3 * i + j) + 136 ≤ E.length by omega_arith), List.drop_take, List.take_take, List.drop_drop]
    rw [show 408 * i + 136 * j = 136 * (3 * i + j) by omega_using [], Nat.min_eq_left (by omega_using [hj])]
  · rename_i hn
    have hA : (E.drop (408 * i)).length = E.length - 408 * i := List.length_drop
    rcases (by omega_using [hj] : j < 2 ∨ j = 2) with hj2 | rfl
    · rw [ite_eq_left (show 136 * (3 * i + j) + 136 ≤ E.length by omega_using [hp, hj2]), List.drop_append_of_le_length (by omega_using [hj, hp, hA]),
        List.take_append_of_le_length (by rw [List.length_drop]; omega_using [hp, hA, hj2]), List.drop_drop,
        show 408 * i + 136 * j = 136 * (3 * i + j) by omega_using []]
    · rw [ite_eq_right (show ¬136 * (3 * i + 2) + 136 ≤ E.length by omega_using [hn]), List.drop_append_of_le_length (by omega_using [hp, hA]), List.drop_drop,
        List.take_of_length_le (by simp only [List.length_append, List.length_drop, List.length_cons,
          List.length_replicate, List.length_nil]; omega_using [hp, hn])]
      simp only [padBlock, List.length_drop, List.append_assoc, List.cons_append, List.nil_append,
        show 408 * i + 136 * 2 = 136 * (3 * i + 2) by omega_using [],
        show 134 - (E.length - 136 * (3 * i + 2)) = 406 - (E.length - 408 * i) by omega_using [hp]]

/-! ## The entries of a fragment -/

theorem allOk_add3 {k : Nat} {ρ : List Byte} {e : Nat} :
    allOk k ρ (e + 3) ↔ allOk k ρ e ∧ ((List.range 3).all fun t =>
      (sampleNTT minIterations (matSeed ρ ((e + t) / k) ((e + t) % k))).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega_using [he]), fun t ht => h (e + t) (by omega_using [ht])⟩
  · rintro ⟨h, h3⟩ e' he
    rcases (by omega_using [] : e' < e ∨ e ≤ e') with he' | he'
    · exact h e' he'
    · have := h3 (e' - e) (by omega_using [he])
      rwa [Nat.add_sub_cancel' he'] at this

theorem habs_congr (H : Spec.Sha3.State) {f g : Nat → List Byte} :
    ∀ n, (∀ j < n, f j = g j) → SH.habs H f n = SH.habs H g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [SH.habs]
    rw [habs_congr H n fun j hj => h j (by omega_using [hj]), h n (by omega_using [])]

/-- Code whose runs are never related. -/
theorem relFalse {P Q : State → State → Prop} {c : Prog isa} (h : ∀ x y, P x y → False) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp _ _ => (h _ _ hp).elim

end VG.Proof.MlKem.X86_64.EkF

end

end

/-!
# ML-KEM on x86-64: encapsulation hashing the key with 16-bit polynomials, the fragments

As `EkFrag.lean`, for `kemEncaps16`'s layout `K` (`Encaps16.frag`): the
entries of `Â` are 512 bytes each, from `oA` (`MatB16`), and the fragment
`b`, which meets `sampleHKW true` (`BatchHOk16`), has its working space and
the sponge of `H` in `W` (from `oW`). The blocks of `pad(ek)` and their
padding are `EkFrag.lean`'s (`hbE`, `blk`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.EkF16

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.Sha3 (xorAt)
open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk EcWfB)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs)
open VG.Proof.MlKem.HSponge (hstate padBlock)
open VG.Proof.MlKem.X86_64.EkF (blk Partial hstate_blk habs_blk stateAt_keep zeros_ok mov0_ok padList hbE hbE_blk
  allOk_add3 habs_congr)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB padTail hblk frag)
open VG.Impl.MlKem.X86_64.Top16 (aP)

/-! ## The checks of the layout -/

variable (K : Kem16)

/-- A piece writing `ws` keeps `EK`, `ρ` at `SB` and the first `e` entries of `Â`. -/
def fkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool :=
  ecChk K.L ws && keepB (ecB K.L) ws (sc oSB) 32 && (List.range e).all fun e' => keepB (ecB K.L) ws (aP K e') 512

/-- ... and the sponge's state. -/
def hkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool := fkeep K ws e && keepB (ecB K.L) ws (sc (oHS K)) 200

/-- The blocks of fragment `i`. -/
def hbChk (i : Nat) : Bool :=
  (if 408 * i + 408 ≤ K.L.ekLen then copyChk (ecB K.L) (ecW K.L) (sc (oHB K)) (.r14, 408 * i) 408
    else copyChk (ecB K.L) (ecW K.L) (sc (oHB K)) (.r14, 408 * i) (K.L.ekLen - 408 * i) &&
      inB (ecW K.L) (sc (oHB K)) 408 && keepB (ecB K.L) [(sc (oHB K + (K.L.ekLen - 408 * i)), 408 - (K.L.ekLen - 408 * i))]
        (sc (oHB K)) (K.L.ekLen - 408 * i)) &&
  hkeep K [(sc (oHB K), 408)] (3 * i)

/-- The seeds of fragment `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun J => seedsChk (ecB K.L) (ecW K.L) J && hkeep K (seedW J) (3 * i) &&
    keepB (ecB K.L) (seedW J) (sc (oHB K)) 408

/-- The fragment inlined, of fragment `i`. -/
def smChk (i : Nat) : Bool :=
  s4_16Chk (ecB K.L) (ecW K.L) (K.oA + 512 * (3 * i)) K.oW &&
    fkeep K [(sc (K.oA + 512 * (3 * i)), 2048), (sc K.oW, 8192)] (3 * i)

/-- What each piece of the matrix needs of the layout, evaluated for each parameter set. -/
structure Ek16FWf : Prop extends EcWfB K.L where
  ek8 : K.L.ekLen % 8 = 0 ∧ K.L.ekLen < 2 ^ 20
  part : 0 < K.L.ekLen % 136 ∧ K.L.ekLen % 136 < 135
  nbE : 3 * nb K.L = K.L.ekLen / 136 + 1
  nbK : 0 < nb K.L ∧ 3 * nb K.L ≤ K.L.k * K.L.k
  last : 272 < K.L.ekLen - 408 * (nb K.L - 1) ∧ K.L.ekLen - 408 * (nb K.L - 1) < 406 ∧ K.L.ekLen < 408 * nb K.L
  hbk : oHB K + 408 < 2 ^ 31 ∧ 408 * nb K.L < 2 ^ 31
  rC : (copyChk (ecB K.L) (ecW K.L) (sc oSB) (.r14, 384 * K.L.k) 32 && ecChk K.L [(sc oSB, 32)]) = true
  zC : (inB (ecW K.L) (sc (oHS K)) 200 && fkeep K [(sc (oHS K), 200)] 0) = true
  hb : ∀ i < nb K.L, hbChk K i = true
  sd : ∀ i < nb K.L, sdChk K i = true
  sm : ∀ i < nb K.L, smChk K i = true


/-! ## What holds before each fragment -/

/-- Before fragment `i`. -/
structure FI16 (K : Kem16) (σ : State) (i : Nat) (s : State) : Prop where
  ec : EK K.L σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = Enc.rhoE K.L (ekE K.L σ)
  mat : MatB16 K.L.k K.oA (Enc.rhoE K.L (ekE K.L σ)) (3 * i) s
  hs : stateAt s.mem (pa s (sc (oHS K))) = hstate (ekE K.L σ) (3 * i)


variable {K}

/-- A piece that writes `ws` and keeps `r15` keeps `FI`. -/
theorem FI16.keep (W : EcWfB K.L) {σ : State} (hp : (encK K.L).pre σ) {i : Nat} {s s' : State} (h : FI16 K σ i s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (h15 : s'.gpr .r15 = s.gpr .r15)
    (hc : hkeep K ws (3 * i) = true) : FI16 K σ i s' := by
  simp only [hkeep, fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hE, hS⟩, hA⟩, hH⟩ := hc
  have L₀ := h.ec.lay W hp
  exact ⟨h.ec.step W hp hP hE, by rw [L₀.keepBytes hP hS]; exact h.sb,
    ⟨by rw [h15]; exact h.mat.r15, fun e he f hf => L₀.keepPoly16 hP (hA e he) (h.mat.mat e he f hf)⟩,
    by rw [stateAt_keep L₀ hP hH]; exact h.hs⟩


theorem padTail16_ok (K : Kem16) {rbs wbs : List (Reg × Nat)} {s : State} (Lx : Lay rbs wbs s) {len : Nat}
    (hlen : len < 406) (h8 : len % 8 = 0) (hin : inB wbs (sc (oHB K)) 408 = true) {d : Nat} (hd : d < 256) :
    WP isa (.block (padTail K len d)) s fun s' => PPost s s' [(sc (oHB K + len), 408 - len)] ∧
      bytesAt s'.mem (pa s (sc (oHB K + len))) (408 - len) =
        BitVec.ofNat 8 d :: (List.replicate (406 - len) 0 ++ [BitVec.ofNat 8 0x80]) := by
  have hc := Lx.cW hin
  have hw : ∀ d n, d + n ≤ 408 → InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (oHB K + d)) n :=
    fun d n h => by
      have := hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base (pa s (sc (oHB K))) h (by omega_using [h])⟩
      rwa [show pa s (sc (oHB K)) = s.gpr .rbx + BitVec.ofNat 64 (oHB K) from rfl, off_add] at this
  unfold padTail
  rw [← List.singleton_append, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mov0_ok s) fun s₁ ⟨h0, hm1, k1⟩ => ?_
  have e1 : s₁.gpr .rbx = s.gpr .rbx := k1.1 .rbx (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok .rbx (oHB K + len) ((408 - len) / 8) s₁ h0 (by omega_using []) fun j hj => by
    rw [k1.2.2, e1, off_add, Nat.add_assoc]; exact hw (len + 8 * j) 8 (by omega_using [hj])) fun s₂ ⟨k2, f2, z2⟩ => ?_
  have e2 : s₂.gpr .rbx = s.gpr .rbx := by rw [k2.1 .rbx (by simp), e1]
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok (sc (oHB K + len)) d (show Reg.rbx ≠ .rax by decide) hd s₂ (by
    show InRegions s₂.wr (s₂.gpr .rbx + BitVec.ofNat 64 (oHB K + len)) 1
    rw [k2.2.2, k1.2.2, e2, ← Nat.add_zero len]; exact hw _ 1 (by omega_using [hlen]))) fun s₃ ⟨m3, k3⟩ => ?_
  have e3 : s₃.gpr .rbx = s.gpr .rbx := by rw [k3.1 .rbx (by decide), e2]
  refine WP.mono (setB_ok (sc (oHB K + 407)) 0x80 (show Reg.rbx ≠ .rax by decide) (by decide) s₃ (by
    show InRegions s₃.wr (s₃.gpr .rbx + BitVec.ofNat 64 (oHB K + 407)) 1
    rw [k3.2.2, k2.2.2, k1.2.2, e3]; exact hw _ 1 (by omega_using []))) fun s₄ ⟨m4, k4⟩ => ?_
  have p6 : pa s₂ (sc (oHB K + len)) = pa s (sc (oHB K + len)) := by
    show s₂.gpr .rbx + _ = s.gpr .rbx + _; rw [e2]
  have p8 : pa s₃ (sc (oHB K + 407)) = pa s (sc (oHB K + len)) + BitVec.ofNat 64 (407 - len) := by
    show s₃.gpr .rbx + _ = s.gpr .rbx + _ + _; rw [e3, off_add, Nat.add_assoc, Nat.add_sub_cancel' (by omega_using [hlen])]
  have hn8 : 8 * ((408 - len) / 8) = 408 - len := by omega_using [h8]
  rw [hn8, e1] at f2 z2
  rw [p6] at m3
  rw [p8] at m4
  have hR : ∀ d n, d + n ≤ 408 - len →
      (⟨pa s (sc (oHB K + len)), 408 - len⟩ : Region).Contains (pa s (sc (oHB K + len)) + BitVec.ofNat 64 d) n :=
    fun d n h => Offset.contains_base _ h (by omega_using [h])
  refine ⟨post_of_keep (((k1.trans k2).trans k3).trans k4) (by decide) ?_, ?_⟩
  · show Frame [⟨pa s (sc (oHB K + len)), 408 - len⟩] s.mem s₄.mem
    rw [m4, m3, ← hm1]
    refine (f2.writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ (hR _ 1 (by omega_using [hlen]))
    have := hR 0 1 (by omega_using [hlen])
    rwa [BitVec.add_zero] at this
  · have z : bytesAt s₂.mem (pa s (sc (oHB K + len))) (408 - len) = List.replicate (408 - len) 0 := by
      refine List.ext_getElem (by simp [bytesAt]) fun i h₁ _ => ?_
      simp only [bytesAt, List.length_map, List.length_range] at h₁
      simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact z2 i h₁
    have w6 := bytesAt_writeW8 s₂.mem (pa s (sc (oHB K + len))) (i := 0) (len := 408 - len) (by omega_using [hlen])
      (by omega_using []) (BitVec.ofNat 8 d)
    rw [BitVec.add_zero] at w6
    rw [m4, bytesAt_writeW8 _ _ (by omega_using [hlen]) (by omega_using []), m3, w6, z, show 408 - len = 406 - len + 2 by omega_using [hlen],
      show 407 - len = 406 - len + 1 by omega_using [hlen], padList]


theorem hblk16_ok (F : Ek16FWf K) {σ : State} (hp : (encK K.L).pre σ) {i : Nat} (hi : i < nb K.L) {s : State}
    (h : FI16 K σ i s) :
    WP isa (hblk K i) s fun s' => PPostB s s' [(sc (oHB K), 408)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s (sc (oHB K))) 408 = hbE (ekE K.L σ) i := by
  have L₀ := h.ec.lay F.toEcWfB hp
  have hc := F.hb i hi
  have hE : (ekE K.L σ).length = K.L.ekLen := bytesAt_length _ _ _
  have ek := h.ec.ek
  unfold hbChk at hc
  unfold hblk hbE
  rw [hE]
  by_cases hf : 408 * i + 408 ≤ K.L.ekLen
  · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
    refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hc.1) fun s' ⟨hP, hb⟩ =>
      ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    rw [hb, ← ek, bytesAt_slice _ _ hf, pa, pa, off_add, Nat.zero_add]
  · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
    obtain ⟨⟨⟨hcp, hin⟩, hkp⟩, -⟩ := hc
    have hl := F.last
    have hn := F.nbE
    have hii : i = nb K.L - 1 := by omega_using [hi, hf, hl]
    have hlen : 272 < K.L.ekLen - 408 * i ∧ K.L.ekLen - 408 * i < 406 := by rw [hii]; exact ⟨hl.1, hl.2.1⟩
    have h8 : (K.L.ekLen - 408 * i) % 8 = 0 := by have := F.ek8.1; omega_using [this]
    refine WP.seq (WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hcp) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
    have L₁ := L₀.post hP₁.b (ecB_bases K.L)
    refine WP.mono (padTail16_ok K L₁ hlen.2 h8 hin (d := 6) (by decide)) fun s₂ ⟨hP₂, hb₂⟩ => ?_
    have e : pa s (sc (oHB K + (K.L.ekLen - 408 * i))) = pa s (sc (oHB K)) + BitVec.ofNat 64 (K.L.ekLen - 408 * i) :=
      (off_add _ _ _).symm
    have hP : PPost s s₂ [(sc (oHB K), 408)] := by
      refine (PPost.trans hP₁ hP₂ (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact rbx_cs)
        (ws := [(sc (oHB K), K.L.ekLen - 408 * i), (sc (oHB K + (K.L.ekLen - 408 * i)), 408 - (K.L.ekLen - 408 * i))])
        (fun w hw => List.mem_cons.2 (.inl (List.mem_singleton.1 hw)))
        (fun w hw => List.mem_cons.2 (.inr hw))).weaken fun w hw => ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Region.sub_prefix (by omega)
      · show Region.Sub ⟨pa s (sc (oHB K + (K.L.ekLen - 408 * i))), _⟩ ⟨pa s (sc (oHB K)), 408⟩
        rw [e]; exact Offset.sub_base _ (by omega_using [hf])
    refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    have k₁ := L₁.keepBytes hP₂.b hkp
    rw [hP₂.pa rbx_cs, hP₁.pa rbx_cs, hb₁] at k₁
    rw [hP₁.pa rbx_cs] at hb₂
    have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) (K.L.ekLen - 408 * i) (408 - (K.L.ekLen - 408 * i))
    rw [Nat.add_sub_cancel' (by omega_using [hf]), ← e, hb₂, k₁] at sp
    rw [sp, ← ek, bytesAt_drop _ _ (by omega_using [hi, hl]), pa, pa, off_add, Nat.zero_add]


/-- The step of three entries. -/
theorem MatB16.three {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB16 K.L.k K.oA ρ e s) (Lx : Lay rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (aP K e') 512 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 3).all (fun t => (sampleNTT minIterations
          (matSeed ρ ((e + t) / K.L.k) ((e + t) % K.L.k))).isSome) then 1 else 0)))
    (hres : ∀ t < 3, ∀ f, sampleNTT minIterations (matSeed ρ ((e + t) / K.L.k) ((e + t) % K.L.k)) = some f →
        PolyIsW 16 s'.mem (pa s (sc (K.oA + 512 * e + 512 * t))) f) : MatB16 K.L.k K.oA ρ (e + 3) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, and_acc h.r15]
    exact ite_congr (propext allOk_add3.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega_using [] : e' < e ∨ e ≤ e') with he'' | he''
    · exact Lx.keepPoly16 hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega_using [he']) f (by rw [Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases]
      rwa [show K.oA + 512 * e + 512 * (e' - e) = K.oA + 512 * e' by omega_using [he'']] at this


/-- While the seeds of fragment `i` are written. -/
structure SI16 (K : Kem16) (σ : State) (i J : Nat) (s : State) : Prop where
  fi : FI16 K σ i s
  sd : SeedsIs (Enc.rhoE K.L (ekE K.L σ)) K.L.k (3 * i) J s
  hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (ekE K.L σ) i

theorem seedI16_ok (F : Ek16FWf K) {σ : State} (hp : (encK K.L).pre σ) {i : Nat} (hi : i < nb K.L) {J : Nat}
    (hJ : J < 4) {s : State} (h : SI16 K σ i J s) :
    WP isa (seedAt J ((3 * i + J) / K.L.k) ((3 * i + J) % K.L.k)) s (SI16 K σ i (J + 1)) := by
  have W := F.toEcWfB
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨⟨hs, hk⟩, hB⟩ := hsd J hJ
  have L₀ := h.fi.ec.lay W hp
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have := F.nbK
  refine WP.mono (seed_step L₀ (ecB_bases K.L) (by omega_using [hi, hJ, h16, this]) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.fi.keep W hp hP.b (hP.cs .r15 (by decide)) hk, hS, ?_⟩
  rw [L₀.keepBytes hP.b hB]; exact h.hb

theorem blocks16_eq (F : Ek16FWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {s : State}
    (hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (ekE K.L σ) i) {j : Nat} (hj : j < 3) :
    bytesAt s.mem (pa s (sc (K.oW)) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
      blk (ekE K.L σ) (3 * i + j) := by
  have hE : (ekE K.L σ).length = K.L.ekLen := bytesAt_length _ _ _
  have hl := F.last
  have hn := F.nbE
  rw [← hbE_blk hj (by rw [hE]; omega_using [hi, hl]), ← hb, bytesAt_slice _ _ (by omega_using [hj])]
  show bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
    bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW + Sample4.oHB) + BitVec.ofNat 64 (136 * j)) 136
  rw [off_add, off_add, Nat.add_assoc]

theorem frag16_ok (F : Ek16FWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} (hp : (encK K.L).pre σ) {i : Nat}
    (hi : i < nb K.L) {s : State} (h : FI16 K σ i s) : WP isa (frag K b i) s (FI16 K σ (i + 1)) := by
  have W := F.toEcWfB
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.hb i hi
  simp only [hbChk, Bool.and_eq_true] at hc
  unfold frag
  refine WP.seq (WP.mono (hblk16_ok F hp hi h) fun s₁ ⟨hP₁, h15₁, hb₁⟩ => ?_)
  have f₁ := h.keep W hp hP₁ h15₁ hc.2
  have i₁ : SI16 K σ i 0 s₁ := ⟨f₁, ⟨f₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    by rw [hP₁.pa rbx_bases]; exact hb₁⟩
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 0) (by decide) i₁) fun s₂ i₂ => ?_)
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 1) (by decide) i₂) fun s₃ i₃ => ?_)
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 2) (by decide) i₃) fun s₄ i₄ => ?_)
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 3) (by decide) i₄) fun s₅ i₅ => ?_)
  have L₅ := i₅.fi.ec.lay W hp
  refine WP.mono (sampleHAt16_ok hb (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  have hk := hsm.2
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
  obtain ⟨⟨hE, hS⟩, hA⟩ := hk
  have hl := F.last
  have hn := F.nbE
  have hpart : Partial (ekE K.L σ) := by
    rw [Partial, show (ekE K.L σ).length = K.L.ekLen from bytesAt_length _ _ _]; exact F.part
  have hlen : (ekE K.L σ).length = K.L.ekLen := bytesAt_length _ _ _
  refine ⟨i₅.fi.ec.step W hp h₆.b hE, by rw [L₅.keepBytes h₆.b hS]; exact i₅.fi.sb, ?_, ?_⟩
  · rw [show 3 * (i + 1) = 3 * i + 3 by omega_using []]
    refine MatB16.three i₅.fi.mat L₅ h₆.b hA ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega_using [hk]))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega_using [ht])]; exact hf)
      rwa [poly4W, pBytes_true, pa, off_add] at this
  · have e1 : pa s₅ (sc (oHS K)) = pa s₅ (sc (K.oW)) + BitVec.ofNat 64 Sample4.oHS := (off_add _ _ _).symm
    rw [h₆.b.pa rbx_bases, e1, h₆.hs, ← e1, i₅.fi.hs,
      habs_congr _ 3 fun j hj => blocks16_eq F hi i₅.hb hj, show 3 * (i + 1) = 3 * i + 3 by omega_using []]
    exact habs_blk hpart (by rw [hlen]; omega_using [hi, hl])

theorem frags16_ok (F : Ek16FWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} (hp : (encK K.L).pre σ) {s : State}
    (h : FI16 K σ 0 s) : WP isa (seqR (frag K b) 0 (nb K.L)) s (FI16 K σ (nb K.L)) := by
  have := seqR_ok (I := FI16 K σ) (nb K.L) 0 (fun k _ hk s hs => frag16_ok F hb hp (by omega_using [hk]) hs) s h
  rwa [Nat.zero_add] at this


end VG.Proof.MlKem.X86_64.EkF16
