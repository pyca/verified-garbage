module

import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
public import VerifiedGarbage.Proof.MlKem.X86_64.PrfBatch
public import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.FragS
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT

/-!
# ML-KEM on x86-64: several outputs of `PRF₂`

In a layout: `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, with
`σ` at `G + 32` (`PrfsPost`), one at a time (`prfsScalar_ok`, `prfsScalar_tr`)
or four at a time with AVX2, but for the first `prfsLead n`, one at a time
(`prfsAvx2_ok`, `prfsAvx2_tr`), whichever implementation of
`vg_mlkem_sample_ntt4` the top-level functions call goes with
(`Callee4.prfs`). Both write within `prfsW` and need what `prfsChk` checks of
the layout.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {rbs wbs : List (Reg × Nat)}

/-! ## Properties of every instruction, piece by piece -/

theorem ctlOk_seq {a b : Prog isa} (ha : ctlOk a = true) (hb : ctlOk b = true) : ctlOk (.seq a b) = true := by
  simp only [ctlOk, ha, hb, Bool.and_self, Bool.or_true]

theorem ctlOk_call {n : String} {c : Prog isa} (h : ctlOk c = true) : ctlOk (.call n c) = true := h

theorem all_call {p : Instr → Bool} {n : String} {c : Prog isa} (h : c.all p = true) :
    (Code.call n c : Prog isa).all p = true := h

theorem ctlOk_ite {c : Cond} {t e : Prog isa} (ht : ctlOk t = true) (he : ctlOk e = true) :
    ctlOk (.ite c t e) = true := by
  simp only [ctlOk, ht, he, Bool.and_self]

theorem all_ite {p : Instr → Bool} {c : Cond} {t e : Prog isa} (ht : t.all p = true) (he : e.all p = true) :
    (Code.ite c t e : Prog isa).all p = true := by
  simp only [Code.all, ht, he, Bool.and_self]

theorem ctlOk_loop {c : Cond} {b : Prog isa} (h : ctlOk b = true) : ctlOk (.loop b c) = true := h

theorem all_loop {p : Instr → Bool} {c : Cond} {b : Prog isa} (h : b.all p = true) :
    (Code.loop b c : Prog isa).all p = true := h

theorem all_seq {p : Instr → Bool} {a b : Prog isa} (ha : a.all p = true) (hb : b.all p = true) :
    (Code.seq a b : Prog isa).all p = true := by
  simp only [Code.all, ha, hb, Bool.and_self]


/-! ## What a piece writes, weakened -/

/-- `PPost` for larger regions. -/
theorem PPost.weaken {s s' : State} {ws ws' : List (Ptr × Nat)} (h : PPost s s' ws)
    (hs : ∀ w ∈ ws, ∃ w' ∈ ws', Region.Sub (toR s w) (toR s w')) : PPost s s' ws' :=
  ⟨h.rd, h.wr, h.cs, h.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      obtain ⟨w', hw', hsub⟩ := hs w hw
      exact ⟨toR s w', List.mem_append_left _ (List.mem_map_of_mem hw'), hsub⟩
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩⟩

/-! ## One output -/

/-- What `prf1 N out` writes. -/
abbrev prf1W (out : Ptr) : List (Ptr × Nat) := [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (out, 128)]

def prf1Chk (bs wbs : List (Reg × Nat)) (out : Ptr) : Bool :=
  inB bs (sc oNB) 1 && inB wbs (sc oNB) 1 && hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 &&
    keepB bs [(sc oNB, 1)] sigP 32

theorem prf1Chk_spec {bs wbs : List (Reg × Nat)} {out : Ptr} (h : prf1Chk bs wbs out = true) :
    inB bs (sc oNB) 1 = true ∧ inB wbs (sc oNB) 1 = true ∧
      hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 = true ∧ keepB bs [(sc oNB, 1)] sigP 32 = true := by
  simp only [prf1Chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  exact ⟨h0, h1, h2, h3⟩

theorem prf1_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N : Nat} (hN : N < 256)
    {out : Ptr} (hc : prf1Chk (rbs ++ wbs) wbs out = true) :
    WP isa (prf1 N out) s fun s' => PPost s s' (prf1W out) ∧
      bytesAt s'.mem (pa s out) 128 = prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 N) := by
  obtain ⟨_, hNB, hh, hk⟩ := prf1Chk_spec hc
  have hocs : out.1 ∈ calleeSaved := (hashChk_spec hh).2.2.2.2.2
  unfold prf1
  refine WP.seq (WP.mono (setB_okL L (by decide) hN hNB) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (hash_ok hcs hh (by decide) L₁) fun s₂ ⟨hP₂, ho₂⟩ =>
    ⟨PPost.app hP₁ hP₂ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro w (rfl | rfl | rfl) <;>
      first | decide | exact hocs), ?_⟩
  have e1 : pa s₁ (sc oNB) = pa s (sc oNB) := hP₁.pa rbx_cs
  have eo : pa s₁ out = pa s out := hP₁.pa hocs
  have hσ : bytesAt s₁.mem (pa s₁ sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L.keepBytes hP₁.b hk
  rw [← eo, ho₂, prf_pieces (by rw [e1]; exact hb₁), hσ, shake31]
  exact (prf_eq 2 _ _).symm

theorem setNB_taint (N : Nat) :
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) N)) (.block [])).isSome = true := by
  kernel_rfl

theorem prf1_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N : Nat} (hN : N < 256) {out : Ptr}
    (hc : prf1Chk (rbs ++ wbs) wbs out = true) : RelCT isa (LRel rbs wbs) (prf1 N out) (LRel rbs wbs) := by
  obtain ⟨hin, hNB, hh, _⟩ := prf1Chk_spec hc
  unfold prf1
  exact RelCT.seq (LRel.step hcs (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (setNB_taint N))
    fun x Lx => WP.mono (setB_okL Lx (by decide) hN hNB) fun _ h => ⟨_, h.1⟩)
    (LRel.step hcs (hash_tr hcs hh (by decide)) fun x Lx => WP.mono (hash_ok hcs hh (by decide) Lx) fun _ h => ⟨_, h.1⟩)

theorem prf1_ctl (N : Nat) (out : Ptr) : ctlOk (prf1 N out) = true := by kernel_rfl

theorem prf1_sp (N : Nat) (out : Ptr) : (prf1 N out).all (fun i => !isa.writesSp i) = true := by kernel_rfl

/-! ## Several outputs -/

/-- What `prfs N₀ n o wl` writes, of either implementation: the index `N`,
the Keccak state and the sponge functions' working space, 2368 bytes of
working space from lane `wl`, and the outputs. -/
abbrev prfsW (n o wl : Nat) : List (Ptr × Nat) :=
  [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (sc (32 * wl), 2368), (sc o, 128 * n)]

/-- What `prfs N₀ n o wl` needs of the layout, of either implementation:
for each output, what computing it on its own needs, and that this keeps `σ`
and the outputs before it; and that the working space, the outputs and `σ`
are apart. -/
def prfsChk (bs wbs : List (Reg × Nat)) (n o wl : Nat) : Bool :=
  (List.range n).all (fun i => prf1Chk bs wbs (sc (o + 128 * i)) && keepB bs (prf1W (sc (o + 128 * i))) sigP 32 &&
    (List.range i).all fun j => keepB bs (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128) &&
  wrOk bs wbs (sc (32 * wl)) 2368 && wrOk bs wbs (sc o) (128 * n) && rdOk bs sigP 32 &&
  sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) && sepB bs (sc (32 * wl)) 2368 sigP 32 &&
  sepB bs (sc o) (128 * n) sigP 32 && decide (32 * wl + 2368 < 2 ^ 31) && decide (o + 128 * n < 2 ^ 31)

theorem prfsChk_spec {bs wbs : List (Reg × Nat)} {n o wl : Nat} (h : prfsChk bs wbs n o wl = true) :
    (∀ i < n, prf1Chk bs wbs (sc (o + 128 * i)) = true ∧ keepB bs (prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, keepB bs (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) ∧
    wrOk bs wbs (sc (32 * wl)) 2368 = true ∧ wrOk bs wbs (sc o) (128 * n) = true ∧ rdOk bs sigP 32 = true ∧
    sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) = true ∧ sepB bs (sc (32 * wl)) 2368 sigP 32 = true ∧
    sepB bs (sc o) (128 * n) sigP 32 = true ∧ 32 * wl + 2368 < 2 ^ 31 ∧ o + 128 * n < 2 ^ 31 := by
  simp only [prfsChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨fun i hi => ⟨(h0 i hi).1.1, (h0 i hi).1.2, (h0 i hi).2⟩, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- What `prfs N₀ n o wl` leaves, from `s`. -/
def PrfsPost (s : State) (N₀ n o wl : Nat) (s' : State) : Prop :=
  PPost s s' (prfsW n o wl) ∧
    ∀ i < n, bytesAt s'.mem (pa s (sc (o + 128 * i))) 128 =
      prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 (N₀ + i))

/-! ## One at a time -/

/-- Output `i` lies within the outputs. -/
theorem out_sub (s : State) {n o i : Nat} (hi : i < n) :
    Region.Sub (toR s (sc (o + 128 * i), 128)) (toR s (sc o, 128 * n)) :=
  show Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ ⟨s.gpr .rbx + BitVec.ofNat 64 o, 128 * n⟩ from
    Offset.sub _ (by omega) (by omega)

/-- After the first `k` outputs. -/
structure ScInv (s : State) (N₀ n o wl k : Nat) (s' : State) : Prop where
  post : PPost s s' (prfsW n o wl)
  sig : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32
  outs : ∀ j < k, bytesAt s'.mem (pa s (sc (o + 128 * j))) 128 =
    prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 (N₀ + j))

/-- The first `r` of `n` outputs, one at a time. -/
theorem prfsScalar_lead {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ r n o wl : Nat}
    (hN : N₀ + r ≤ 256) (hr : r ≤ n)
    (hs : ∀ i < r, prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true ∧
      keepB (rbs ++ wbs) (prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, keepB (rbs ++ wbs) (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) :
    WP isa (prfsScalar N₀ r o wl) s (ScInv s N₀ n o wl r) := by
  have h := seqR_ok (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (I := ScInv s N₀ n o wl) r 0
    (fun k _ hk s₁ h₁ => by
      obtain ⟨c1, cs, cj⟩ := hs k (by omega)
      have L₁ := L.post h₁.post.b hcs
      refine WP.mono (prf1_ok L₁ hcs (by omega) c1) fun s₂ ⟨hP, hb⟩ => ?_
      have e₁ : ∀ x, pa s₁ (sc x) = pa s (sc x) := fun x => h₁.post.pa rbx_cs
      refine ⟨PPost.trans h₁.post (hP.weaken fun w hw => ?_) (fun w hw => by
          simp only [prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact rbx_cs) (fun w hw => hw) (fun w hw => hw),
        by rw [L₁.keepBytes hP.b cs]; exact h₁.sig, fun j hj => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
        · exact ⟨_, by simp, out_sub s₁ (o := o) (show k < n by omega)⟩
      · rcases (by omega : j < k ∨ j = k) with hj | rfl
        · rw [← e₁, ← hP.pa rbx_cs, L₁.keepBytes hP.b (cj j hj), e₁]; exact h₁.outs j hj
        · rw [← e₁, hb, h₁.sig])
    s ⟨Post.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact WP.mono h fun s' h' => by rwa [Nat.zero_add] at h'

theorem prfsScalar_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsScalar N₀ n o wl) s (PrfsPost s N₀ n o wl) :=
  WP.mono (prfsScalar_lead L hcs (by omega) (Nat.le_refl n) (prfsChk_spec hc).1) fun _ h' => ⟨h'.post, h'.outs⟩

theorem prfsScalar_trL (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ r o wl : Nat} (hN : N₀ + r ≤ 256)
    (hs : ∀ i < r, prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true) :
    RelCT isa (LRel rbs wbs) (prfsScalar N₀ r o wl) (LRel rbs wbs) := by
  have := seqR_tr (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (R := fun _ => LRel rbs wbs) r 0 fun k _ hk =>
    prf1_tr hcs (by omega) (hs k (by omega))
  exact this

theorem prfsScalar_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (LRel rbs wbs) (prfsScalar N₀ n o wl) fun _ _ => True :=
  RelCT.mono (prfsScalar_trL hcs (by omega) fun i hi => ((prfsChk_spec hc).1 i hi).1) (fun _ _ h => h)
    fun _ _ _ => trivial

theorem ctlOk_seqR {f : Nat → Prog isa} (h : ∀ k, ctlOk (f k) = true) : ∀ n a, ctlOk (seqR f a n) = true
  | 0, _ => rfl
  | n + 1, a => ctlOk_seq (h a) (ctlOk_seqR h n (a + 1))

theorem all_seqR {p : Instr → Bool} {f : Nat → Prog isa} (h : ∀ k, (f k).all p = true) :
    ∀ n a, (seqR f a n).all p = true
  | 0, _ => rfl
  | n + 1, a => all_seq (h a) (all_seqR h n (a + 1))

theorem prfsScalar_ctl (N₀ n o wl : Nat) : ctlOk (prfsScalar N₀ n o wl) = true :=
  ctlOk_seqR (fun _ => prf1_ctl _ _) n 0

theorem prfsScalar_sp (N₀ n o wl : Nat) : (prfsScalar N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  all_seqR (fun _ => prf1_sp _ _) n 0

/-! ## Four at a time -/

namespace Prf4

open VG.Impl.MlKem.X86_64.Prf4

/-- What `prfsX4 N₀ n o wl` needs, with `scratch` at `b`. -/
structure RawPre (b : Addr) (n o wl : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = b
  w : InRegions s.wr (sP b wl) 2368
  out : InRegions s.wr (b + BitVec.ofNat 64 o) (128 * n)
  sig : InRegions (s.rd ++ s.wr) (sS b) 32
  dWO : (wR b wl).Disjoint (oR b o n)
  dWS : (wR b wl).Disjoint (sR b)
  dOS : (oR b o n).Disjoint (sR b)
  small : 32 * wl + 2368 < 2 ^ 31
  so : o + 128 * n < 2 ^ 31

theorem lt64 {a o : Nat} (h : o + a < 2 ^ 32) : a < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))

theorem RawPre.bpre {b : Addr} {n o wl : Nat} {s : State} (h : RawPre b n o wl s) {m : Nat} (hm : m ≤ 4)
    (hmn : m ≤ n) : BPre b wl o m s := by
  have hs : Region.Sub (oR b o m) (oR b o n) := Region.sub_prefix (by omega)
  refine ⟨h.rbx, h.w, ?_, h.sig, h.dWO.sub_right hs, h.dWS, h.dOS.sub_left hs, hm, h.small⟩
  have := inRegions_sub h.out (off := 0) (l := 128 * m) (by omega) (lt64 (o := o) (a := 128 * n) (by have := h.so; omega))
  rwa [add_ofNat_zero] at this

/-- Between the pieces of `prfsX4`, from `s₀`: `BEnv` but for `r8`–`r10`,
which hold the loop's pointer, index and count. -/
structure XEnv (b : Addr) (wl o n : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cs : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  frame : Frame [wR b wl, oR b o n] s₀.mem s.mem

theorem XEnv.refl {b : Addr} {wl o n : Nat} {s : State} : XEnv b wl o n s s :=
  ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem XEnv.keep {b : Addr} {wl o n : Nat} {s₀ s s' : State} (h : XEnv b wl o n s₀ s) (hm : s'.mem = s.mem)
    {rs : List Reg} (k : Keep rs s s') (hrs : ∀ r ∈ calleeSaved, r ∉ rs) : XEnv b wl o n s₀ s' :=
  ⟨k.2.1.trans h.rd, k.2.2.trans h.wr, fun r hr => (k.gpr (hrs r hr)).trans (h.cs r hr), by rw [hm]; exact h.frame⟩

/-- `XEnv` after a batch writing outputs `d, …, d + m - 1` of `n`. -/
theorem XEnv.batch {b : Addr} {wl o n d m : Nat} {s₀ s s' : State} (h : XEnv b wl o n s₀ s)
    (e : BEnv b wl (o + 128 * d) m s s') (hs : d + m ≤ n) : XEnv b wl o n s₀ s' := by
  have hsub : Region.Sub (oR b (o + 128 * d) m) (oR b o n) := Offset.sub _ (by omega) (by omega)
  refine ⟨e.rd.trans h.rd, e.wr.trans h.wr, fun r hr => (e.cs r (List.mem_append_left _ hr)).trans (h.cs r hr),
    h.frame.trans (e.frame.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hsub⟩

/-- What a part of `prfsX4` needs: `RawPre` for outputs `d, …, d + m - 1`
of `n`. -/
theorem RawPre.shift {b : Addr} {n o wl : Nat} {s₀ s : State} (h : RawPre b n o wl s₀) (he : XEnv b wl o n s₀ s)
    {d m : Nat} (hle : d + m ≤ n) : RawPre b m (o + 128 * d) wl s := by
  have so := h.so
  have hsub : Region.Sub (oR b (o + 128 * d) m) (oR b o n) := Offset.sub _ (by omega) (by omega)
  refine ⟨(he.cs .rbx (by decide)).trans h.rbx, by rw [he.wr]; exact h.w, ?_, by rw [he.rd, he.wr]; exact h.sig,
    h.dWO.sub_right hsub, h.dWS, h.dOS.sub_left hsub, h.small, by omega⟩
  have := inRegions_sub h.out (off := 128 * d) (l := 128 * m) (by omega) (lt64 (o := o) (a := 128 * n) (by omega))
  rw [he.wr, ← Offset.add_add]; exact this

theorem XEnv.sig {b : Addr} {n o wl : Nat} {s₀ s : State} (h : RawPre b n o wl s₀) (he : XEnv b wl o n s₀ s) :
    sig b s = sig b s₀ :=
  bytesAt_frame he.frame (by simpa using ⟨h.dWS.symm, h.dOS.symm⟩) (by decide)

/-- An output written before a batch of outputs `d, …, d + m - 1`, and not by it. -/
theorem out_kept {b : Addr} {n o wl : Nat} {s₀ s s' : State} (h : RawPre b n o wl s₀) {d m k : Nat}
    (e : BEnv b wl (o + 128 * d) m s s') (hs : d + m ≤ n) (hk : k < d) :
    bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 = bytesAt s.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 := by
  have so := h.so
  have hk' : Region.Sub ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (oR b o n) := Offset.sub _ (by omega) (by omega)
  have hd : Region.Disjoint ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (oR b (o + 128 * d) m) :=
    Offset.disjoint _ (by omega) (by omega) (by omega)
  exact bytesAt_frame e.frame (by simpa using ⟨(h.dWO.sub_right hk').symm, hd⟩) (by decide)

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `regs N₀ o`: `r8 := scratch + o`, `r9 := N₀`. -/
theorem regs_ok {b : Addr} {s : State} (hb : s.gpr .rbx = b) {N₀ o : Nat} (ho : o < 2 ^ 31) (hN : N₀ < 2 ^ 31) :
    WP isa (.block (regs N₀ o)) s fun s' => (s'.gpr .r8 = b + BitVec.ofNat 64 o ∧
      s'.gpr .r9 = BitVec.ofNat 64 N₀ ∧ s'.mem = s.mem) ∧ Keep [.r8, .r9] s s' :=
  WP.keep _ (by unfold regs; xrun [hb, sx_ofNat ho, zx_ofNat (show N₀ < 2 ^ 32 by omega)]) rfl

/-- After `i` batches of four of `quads N₀ q o wl`, from `s₀`. -/
structure QInv (b : Addr) (wl N₀ q o : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  env : XEnv b wl o (4 * q) s₀ s
  r8 : s.gpr .r8 = b + BitVec.ofNat 64 (o + 128 * (4 * i))
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N₀ + 4 * i)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (q - i)
  out : ∀ k < 4 * i, bytesAt s.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
    prf 2 (sig b s₀) (BitVec.ofNat 8 (N₀ + k))

theorem quads_ok {fast : Bool} {b : Addr} {wl N₀ q o : Nat} {s : State} (h : RawPre b (4 * q) o wl s)
    (hq : 0 < q) (hN : N₀ + 4 * q + 4 ≤ 256) :
    WP isa (quads N₀ q o wl fast) s fun s' => XEnv b wl o (4 * q) s s' ∧
      ∀ k < 4 * q, bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
        prf 2 (sig b s) (BitVec.ofNat 8 (N₀ + k)) := by
  have so := h.so
  unfold quads
  refine WP.seq (WP.mono (show WP isa (.block (regs N₀ o ++ ([.mov32 .r10 (.imm (BitVec.ofNat 32 q))] : List Instr))) s
    (QInv b wl N₀ q o s 0) from ?_) fun t h0 => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (regs_ok h.rbx (N₀ := N₀) (o := o) (by omega) (by omega)) fun s₁ ⟨⟨h8, h9, hm₁⟩, k₁⟩ => ?_
    refine WP.mono (WP.keep [.r10] (Q := fun s₂ => s₂.gpr .r10 = BitVec.ofNat 64 q ∧ s₂.mem = s₁.mem)
      (by xrun [zx_ofNat (show q < 2 ^ 32 by omega)]) rfl) fun s₂ ⟨⟨h10, hm₂⟩, k₂⟩ => ?_
    refine ⟨(XEnv.refl.keep hm₁ k₁ (by decide)).keep hm₂ k₂ (by decide), ?_, ?_, by rw [h10, Nat.sub_zero],
      fun k hk => absurd hk (by omega)⟩
    · rw [k₂.gpr (by decide), h8]; simp only [Nat.mul_zero, Nat.add_zero]
    · rw [k₂.gpr (by decide), h9]; simp only [Nat.mul_zero, Nat.add_zero]
  refine VG.Proof.Bignum.X86_64.wp_upto (a := 0) (N := q) hq (QInv b wl N₀ q o s) (fun i _ hi t hI => ?_)
    (fun t hI => ⟨hI.env, hI.out⟩) h0
  have raw := h.shift hI.env (d := 4 * i) (m := 4) (by omega)
  have hsig := XEnv.sig h hI.env
  refine WP.seq (WP.mono (batch_ok (fast := fast) (raw.bpre (by decide) (by decide)) (N₀ := N₀ + 4 * i) (by omega)
    hI.r8 hI.r9) fun t₁ ⟨e₁, r₁⟩ => ?_)
  have h8 : t₁.gpr .r8 = b + BitVec.ofNat 64 (o + 128 * (4 * i)) := (e₁.cs .r8 (by decide)).trans hI.r8
  have h9 : t₁.gpr .r9 = BitVec.ofNat 64 (N₀ + 4 * i) := (e₁.cs .r9 (by decide)).trans hI.r9
  have h10 : t₁.gpr .r10 = BitVec.ofNat 64 (q - i) := (e₁.cs .r10 (by decide)).trans hI.r10
  have env₁ := hI.env.batch e₁ (by omega)
  refine WP.mono (WP.keep [.r8, .r9, .r10] (Q := fun t₂ => (t₂.gpr .r8 = b + BitVec.ofNat 64 (o + 128 * (4 * (i + 1))) ∧
      t₂.gpr .r9 = BitVec.ofNat 64 (N₀ + 4 * (i + 1)) ∧ t₂.gpr .r10 = BitVec.ofNat 64 (q - (i + 1)) ∧
      t₂.zf = some (decide (i + 1 = q))) ∧ t₂.mem = t₁.mem) (by
    unfold next
    xrun [h8, h9, h10]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show o + 128 * (4 * i) + 512 = o + 128 * (4 * (i + 1)) by omega]
    · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show N₀ + 4 * i + 4 = N₀ + 4 * (i + 1) by omega]
    · rw [ofNat64_pred (by omega) (by omega), show q - i - 1 = q - (i + 1) by omega]
    · rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)) rfl) fun t₂ ⟨⟨⟨h8', h9', h10', hz⟩, hm⟩, k⟩ => ⟨hz, env₁.keep hm k (by decide), h8', h9', h10', fun k hk => ?_⟩
  rw [hm]
  rcases (by omega : k < 4 * i ∨ 4 * i ≤ k) with hk' | hk'
  · rw [out_kept h e₁ (by omega) hk']; exact hI.out k hk'
  · have := r₁ (k - 4 * i) (by omega)
    rwa [hsig, show o + 128 * (4 * i) + 128 * (k - 4 * i) = o + 128 * k by omega,
      show N₀ + 4 * i + (k - 4 * i) = N₀ + k by omega] at this

/-- `prfsX4 N₀ n o wl`: `PRF₂(σ, N₀ + k)` to `scratch + o + 128 k` for each `k < n`. -/
theorem prfsX4_ok {fast : Bool} {b : Addr} {wl N₀ n o : Nat} {s : State} (h : RawPre b n o wl s)
    (hN : N₀ + n + 4 ≤ 256) :
    WP isa (prfsX4 fast N₀ n o wl) s fun s' => XEnv b wl o n s s' ∧
      ∀ k < n, bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
        prf 2 (sig b s) (BitVec.ofNat 8 (N₀ + k)) := by
  have so := h.so
  have hn := Nat.div_add_mod n 4
  have hr := Nat.mod_lt n (show 0 < 4 by decide)
  unfold prfsX4
  generalize n / 4 = q at hn ⊢
  generalize n % 4 = r at hn hr ⊢
  subst hn
  -- The batches of four.
  refine WP.seq (WP.mono (show WP isa (if q = 0 then .block [] else quads N₀ q o wl fast) s (fun s₁ =>
      XEnv b wl o (4 * q + r) s s₁ ∧ ∀ k < 4 * q, bytesAt s₁.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
        prf 2 (sig b s) (BitVec.ofNat 8 (N₀ + k))) from ?_) fun s₁ ⟨e₁, o₁⟩ => ?_)
  · split
    · exact WP.block_nil ⟨XEnv.refl, fun k hk => absurd hk (by omega)⟩
    · have h₀ := h.shift (s := s) XEnv.refl (d := 0) (m := 4 * q) (by omega)
      rw [Nat.mul_zero, Nat.add_zero] at h₀
      refine WP.mono (quads_ok (fast := fast) h₀ (by omega) (by omega)) fun s₁ ⟨e₁, o₁⟩ =>
        ⟨⟨e₁.rd, e₁.wr, e₁.cs, e₁.frame.sub fun r' hr' => ?_⟩, o₁⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  -- The last `r`.
  have hsig := XEnv.sig h e₁
  split
  · exact WP.block_nil ⟨e₁, fun k hk => o₁ k (by omega)⟩
  · have raw := h.shift e₁ (d := 4 * q) (m := r) (by omega)
    refine WP.seq (WP.mono (regs_ok raw.rbx (N₀ := N₀ + 4 * q) (o := o + 512 * q) (by omega) (by omega))
      fun s₂ ⟨⟨h8, h9, hm₂⟩, k₂⟩ => show WP isa (batch r wl fast) s₂ _ from ?_)
    · have raw₂ : RawPre b r (o + 128 * (4 * q)) wl s₂ := raw.shift (XEnv.refl.keep hm₂ k₂ (by decide)) (d := 0) (m := r)
        (by omega) |> fun h => by rwa [Nat.mul_zero, Nat.add_zero] at h
      refine WP.mono (batch_ok (fast := fast) (raw₂.bpre (by omega) (Nat.le_refl _)) (N₀ := N₀ + 4 * q) (by omega)
        (by rw [h8]; congr 2; omega) h9) fun s₃ ⟨e₃, r₃⟩ => ?_
      have e₂ := (e₁.keep hm₂ k₂ (by decide)).batch e₃ (by omega)
      refine ⟨e₂, fun k hk => ?_⟩
      rcases (by omega : k < 4 * q ∨ 4 * q ≤ k) with hk' | hk'
      · rw [out_kept h e₃ (by omega) hk', hm₂]; exact o₁ k hk'
      · have := r₃ (k - 4 * q) (by omega)
        rwa [show sig b s₂ = sig b s by rw [show sig b s₂ = sig b s₁ by simp only [sig, hm₂]]; exact hsig,
          show o + 128 * (4 * q) + 128 * (k - 4 * q) = o + 128 * k by omega,
          show N₀ + 4 * q + (k - 4 * q) = N₀ + k by omega] at this

theorem quads_tr {fast : Bool} (N₀ q o wl : Nat) :
    RelCT isa (fun x y => x.gpr .rbx = y.gpr .rbx) (quads N₀ q o wl fast) fun x y => x.gpr .rbx = y.gpr .rbx := by
  cases fast
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) [.rbx]
      (hc := taint.hintOfSize Taint.chunk (X86_64.Taint.ofRegs [.rbx]) (quads 0 1 0 0 false)) (by kernel_rfl))
      (fun _ _ h => h) fun _ _ h => h _ (List.mem_singleton_self _)
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) [.rbx]
      (hc := taint.hintOfSize Taint.chunk (X86_64.Taint.ofRegs [.rbx]) (quads 0 1 0 0 true)) (by kernel_rfl))
      (fun _ _ h => h) fun _ _ h => h _ (List.mem_singleton_self _)

theorem prfsX4_rtr {fast : Bool} {wl : Nat} (n N₀ o : Nat) :
    RelCT isa (fun x y => x.gpr .rbx = y.gpr .rbx) (prfsX4 fast N₀ n o wl) fun x y => x.gpr .rbx = y.gpr .rbx := by
  unfold prfsX4
  refine RelCT.seq (by split; exacts [nil_tr, quads_tr _ _ _ _]) ?_
  split
  · exact nil_tr
  · refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) [.rbx, .r8, .r9] (hc := .block []) (by kernel_rfl)) ?_
    exact RelCT.mono (batch_tr (fun _ _ h => h) wl (Nat.le_of_lt (Nat.mod_lt n (by decide)))) (fun _ _ h => h)
      fun _ _ h => h _ (List.mem_cons_self ..)

/-- The permutation never loads MXCSR: evaluated once for each implementation. -/
theorem permute4_ctl (fast : Bool) : ctlOk (Impl.Sha3.X86_64.X4.permute4 fast) = true := by
  cases fast <;> kernel_rfl

/-- The permutation never writes the stack pointer: evaluated once for each implementation. -/
theorem permute4_sp (fast : Bool) : (Impl.Sha3.X86_64.X4.permute4 fast).all (fun i => !isa.writesSp i) = true := by
  cases fast <;> kernel_rfl

theorem batch_ctl {fast : Bool} {m : Nat} (wl : Nat) (hm : m < 5) : ctlOk (batch m wl fast) = true :=
  ctlOk_seq (by kernel_rfl) (ctlOk_seq (permute4_ctl fast) (by
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl <;> kernel_rfl))

theorem batch_sp {fast : Bool} {m : Nat} (wl : Nat) (hm : m < 5) :
    (batch m wl fast).all (fun i => !isa.writesSp i) = true :=
  all_seq (by kernel_rfl) (all_seq (permute4_sp fast) (by
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl <;> kernel_rfl))

theorem quads_ctl {fast : Bool} (N₀ q o wl : Nat) : ctlOk (quads N₀ q o wl fast) = true := by
  unfold quads
  exact ctlOk_seq (by kernel_rfl) (ctlOk_loop (ctlOk_seq (batch_ctl wl (by decide)) (by kernel_rfl)))

theorem quads_sp {fast : Bool} (N₀ q o wl : Nat) : (quads N₀ q o wl fast).all (fun i => !isa.writesSp i) = true := by
  unfold quads
  exact all_seq (by kernel_rfl) (all_loop (all_seq (batch_sp wl (by decide)) (by kernel_rfl)))

theorem prfsX4_ctl {fast : Bool} {wl : Nat} (n N₀ o : Nat) : ctlOk (prfsX4 fast N₀ n o wl) = true := by
  unfold prfsX4
  refine ctlOk_seq (by split; exacts [rfl, quads_ctl _ _ _ _]) ?_
  split
  · rfl
  · exact ctlOk_seq (by kernel_rfl) (batch_ctl wl (by have := Nat.mod_lt n (show 0 < 4 by decide); omega))

theorem prfsX4_sp {fast : Bool} {wl : Nat} (n N₀ o : Nat) : (prfsX4 fast N₀ n o wl).all (fun i => !isa.writesSp i) = true := by
  unfold prfsX4
  refine all_seq (by split; exacts [rfl, quads_sp _ _ _ _]) ?_
  split
  · rfl
  · exact all_seq (by kernel_rfl) (batch_sp wl (by have := Nat.mod_lt n (show 0 < 4 by decide); omega))

end Prf4

theorem cover_in {X : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] X) : InRegions X a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem prfsLead_le (n : Nat) : prfsLead n ≤ n := by
  unfold prfsLead; split <;> omega

theorem prfsAvx2_ok {fast : Bool} {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsAvx2 (fast := fast) N₀ n o wl) s (PrfsPost s N₀ n o wl) := by
  obtain ⟨hs, hw, ho, hsg, dwo, dws, dos, hsm, hso⟩ := prfsChk_spec hc
  have hw' : inB wbs (sc (32 * wl)) 2368 = true := ((Bool.and_eq_true _ _).mp hw).2
  have ho' : inB wbs (sc o) (128 * n) = true := ((Bool.and_eq_true _ _).mp ho).2
  obtain ⟨n₀, hn₀, hl⟩ := inB_spec (rdOk_in ((Bool.and_eq_true _ _).mp ho).1)
  have := L.small _ hn₀
  have hb : o + 128 * n < 2 ^ 32 := Nat.lt_of_le_of_lt (show o + 128 * n ≤ n₀ from hl) this
  have i1 := cover_in (L.cW hw')
  have i2 := cover_in (L.cW ho')
  have i3 := cover_in (L.cR (rdOk_in hsg))
  have d1 := L.disj dwo
  have d2 := L.disj dws
  have d3 := L.disj dos
  have hr := prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  refine WP.seq (WP.mono (prfsScalar_lead L hcs (by omega) hr fun i hi => hs i (by omega)) fun s₁ h₁ => ?_)
  have e₁ : s₁.gpr .rbx = s.gpr .rbx := h₁.post.cs .rbx (by decide)
  have hsub : Region.Sub (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) (Prf4.oR (s.gpr .rbx) o n) :=
    Offset.sub _ (by omega) (by omega)
  have raw : Prf4.RawPre (s.gpr .rbx) (n - r) (o + 128 * r) wl s₁ := by
    refine ⟨e₁, by rw [h₁.post.wr]; exact i1, ?_, by rw [h₁.post.rd, h₁.post.wr]; exact i3, d1.sub_right hsub, d2,
      d3.sub_left hsub, hsm, by omega⟩
    have := inRegions_sub i2 (off := 128 * r) (l := 128 * (n - r)) (by omega) (Prf4.lt64 hb)
    rw [h₁.post.wr, ← Offset.add_add]; exact this
  have hsig : Prf4.sig (s.gpr .rbx) s₁ = bytesAt s.mem (pa s sigP) 32 := by
    rw [← h₁.sig]; simp only [Prf4.sig, Prf4.sS, pa, e₁]
  refine WP.mono (Prf4.prfsX4_ok (fast := fast) raw (by omega)) fun s' ⟨e, out⟩ =>
    ⟨PPost.trans h₁.post ⟨e.rd, e.wr, e.cs, e.frame.sub fun r' hr' => ?_⟩ (fun w hw => by
      simp only [prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact rbx_cs) (fun w hw => hw) (fun w hw => hw), fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · refine ⟨toR s₁ (sc (32 * wl), 2368), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))), ?_⟩
      simp only [toR, pa, e₁]; exact fun _ h => h
    · refine ⟨toR s₁ (sc o, 128 * n), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _)))))), ?_⟩
      simp only [toR, pa, e₁]; exact hsub
  · rcases (by omega : i < r ∨ r ≤ i) with hi' | hi'
    · rw [bytesAt_frame e.frame (by
        have hk : Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ (Prf4.oR (s.gpr .rbx) o n) :=
          Offset.sub _ (by omega) (by omega)
        have hd : Region.Disjoint ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩
            (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) := Offset.disjoint _ (by omega) (by omega) (by omega)
        simpa using ⟨(d1.sub_right hk).symm, hd⟩) (by decide)]
      exact h₁.outs i hi'
    · have := out (i - r) (by omega)
      rwa [hsig, show o + 128 * r + 128 * (i - r) = o + 128 * i by omega,
        show N₀ + r + (i - r) = N₀ + i by omega] at this

theorem prfsAvx2_tr {fast : Bool} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (LRel rbs wbs) (prfsAvx2 (fast := fast) N₀ n o wl) fun _ _ => True := by
  obtain ⟨hs, -, -, hsg, -⟩ := prfsChk_spec hc
  have hr := prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  exact RelCT.seq (prfsScalar_trL hcs (by omega) fun i hi => (hs i (by omega)).1)
    (RelCT.mono (Prf4.prfsX4_rtr _ _ _) (fun _ _ h => h.eq (rdOk_in hsg)) fun _ _ _ => trivial)

theorem prfsAvx2_ctl {fast : Bool} (N₀ n o wl : Nat) : ctlOk (prfsAvx2 (fast := fast) N₀ n o wl) = true :=
  ctlOk_seq (prfsScalar_ctl _ _ _ _) (Prf4.prfsX4_ctl _ _ _)

theorem prfsAvx2_sp {fast : Bool} (N₀ n o wl : Nat) : (prfsAvx2 (fast := fast) N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  all_seq (prfsScalar_sp _ _ _ _) (Prf4.prfsX4_sp _ _ _)

end VG.Proof.MlKem.X86_64
