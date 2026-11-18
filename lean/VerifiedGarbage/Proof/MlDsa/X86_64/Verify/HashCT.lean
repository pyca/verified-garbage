module

public import VerifiedGarbage.Proof.MlKem.X86_64.KCall
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Entry
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.KCall
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Entry
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.Zero
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.Mem

/-! ### `MlDsa.X86_64.Verify.Hash`, which this module and modules that import it used -/

section

/-!
# ML-DSA verification on x86-64: `H(a ‖ b)` through the sponge

`hash2 a la b lb out len` zeroes the Keccak state at `scratch`, absorbs the
`la` bytes at `a` and the `lb` bytes at `b`, pads with SHAKE's suffix and
squeezes `len` bytes to `out`: `H(a ‖ b, len)` (`hash2_ok`), leaking only the
addresses (`hash2_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates Repr squeezeFrom)

/-! ## The checks -/

/-- The state and the working space of the sponge, apart, writable. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  sepB bs (sc 0) 200 (sc 200) 640 && inB bs (sc 0) 200 && inB bs (sc 200) 640 && inB wbs (sc 0) 200 &&
    inB wbs (sc 200) 640

/-- A piece to absorb, apart from the sponge. -/
def pieceChk (bs : List (Reg × Nat)) (p : Ptr) (l : Nat) : Bool :=
  sepB bs p l (sc 0) 200 && sepB bs p l (sc 200) 640 && inB bs p l

/-- The output, apart from the sponge, writable. -/
def outChk (bs wbs : List (Reg × Nat)) (p : Ptr) (l : Nat) : Bool :=
  sepB bs p l (sc 0) 200 && sepB bs p l (sc 200) 640 && inB bs p l && inB wbs p l

/-- The checks of `hash2`. -/
def hashChk (bs wbs : List (Reg × Nat)) (a : Ptr) (la : Nat) (b : Ptr) (lb : Nat) (out : Ptr) (len : Nat) : Bool :=
  kChk bs wbs && pieceChk bs a la && pieceChk bs b lb && outChk bs wbs out len &&
    keepB bs [(sc 0, 200)] a la && keepB bs [(sc 0, 200)] b lb && keepB bs [(sc 0, 200), (sc 200, 640)] b lb &&
    decide (la < 136) && decide (0 < la)

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
include L

theorem kChk_spec (h : kChk (rbs ++ wbs) wbs = true) :
    Region.Disjoint ⟨pa s (sc 0), 200⟩ ⟨pa s (sc 200), 640⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 200⟩ ∧
      (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 200), 640⟩ ∧ Covers [⟨pa s (sc 0), 200⟩] s.wr ∧
      Covers [⟨pa s (sc 200), 640⟩] s.wr := by
  simp only [kChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := h
  exact ⟨L.disj c1, L.stkD c2, L.stkD c3, L.cW c4, L.cW c5⟩

end

/-! ## Zeroing the state -/

theorem kzero_ok (s : State) (hw : Covers [⟨pa s (sc 0), 200⟩] s.wr) :
    WP isa (.block kzero) s fun s' => PPostB s s' [(sc 0, 200)] ∧ s'.gpr .r15 = s.gpr .r15 ∧ stateAt s'.mem (pa s (sc 0)) = Spec.Sha3.zero := by
  rw [kzero, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = s.mem ∧ s1.gpr .rax = 0) (by xrun) (Proof.MlKem.X86_64.writesOnly_of (by decide)))
    fun s1 ⟨⟨hm, hax⟩, k1⟩ => ?_
  have hbx : s1.gpr .rbx = s.gpr .rbx := k1.gpr (by decide)
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => ?_) fun s2 ⟨hz, hf, k2⟩ => ?_
  · rw [k1.2.2, hbx]
    exact hw _ _ ⟨_, List.mem_singleton_self _, contains_offset' (by omega_using [hi]) (by omega_using [])⟩
  · rw [hbx] at hz hf
    exact ⟨postB_of_keep (k1.trans k2) (by decide) (by rw [← hm]; exact hf), (k1.trans k2).gpr (by decide), hz⟩

/-! ## The calls -/

theorem r15_call {s s1 s' : State} {as : List (Reg × Arg)} (h1 : Args as s s1)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s1.gpr r) : s'.gpr .r15 = s.gpr .r15 :=
  (hcs _ (by decide)).trans (h1.2.gpr (by decide))

abbrev kabsArgs (src : Ptr) (len rate pos : Nat) : List (Reg × Arg) :=
  [(.rdi, .ptr (sc 0)), (.rsi, .imm rate), (.rdx, .imm pos), (.rcx, .ptr src), (.r8, .imm len), (.r9, .ptr (sc 200))]

theorem kabs_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len pos : Nat} (hp : pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136) :
    WP isa (kabs src len 136 pos) s fun s' => PPostB s s' [(sc 0, 200), (sc 200, 640)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) 136 msg → pos = msg.length % 136 →
        Repr s'.mem (pa s (sc 0)) 136 (msg ++ bytesAt s.mem (pa s src) len) := by
  obtain ⟨d1, k1, k2, w1, w2⟩ := kChk_spec L hk
  simp only [pieceChk, Bool.and_eq_true] at hp
  obtain ⟨⟨p1, p2⟩, p3⟩ := hp
  have hS := L.ok
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec p3; have := (hS _ hn).1; omega
  have ha : ∀ a ∈ kabsArgs src len 136 pos, a.2.Ok ∧ a.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    have c0 : inB (rbs ++ wbs) (sc 0) 200 = true := by
      simp only [kChk, Bool.and_eq_true] at hk; exact hk.1.1.1.2
    have c1 : inB (rbs ++ wbs) (sc 200) 640 = true := by
      simp only [kChk, Bool.and_eq_true] at hk; exact hk.1.1.2
    exact ⟨⟨ptr_ok hS c0, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩, ⟨show pos < 2 ^ 31 by omega_using [hpos], by decide⟩,
      ⟨ptr_ok hS p3, by decide⟩, ⟨hlen, by decide⟩, ⟨ptr_ok hS c1, by decide⟩⟩
  refine WP.seq (WP.mono (glue_ok' ha (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : Args (kabsArgs src len 136 pos) s s1) => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  have kk : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 16).Disjoint R :=
    fun h => by rw [hsp]; exact h.sub_left (below_sub (by omega_using []) (by omega_using []))
  refine absorb_call ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, hpos, by omega_using [hlen], d1, (L.disj p1),
    (L.disj p2), kk k1, kk (L.stkD p3), kk k2⟩
    (by rw [h1.2.2.1, h1.2.2.2]; exact Covers.append_left (L.cR p3) (Covers.right (Covers.cons w1 w2)))
    (by rw [h1.2.2.2]; exact Covers.cons w1 w2) (fun s' hrd hwr hcs hf hR _ => ?_)
  have hb : ∀ r ∈ bases, s'.gpr r = s.gpr r := by
    intro r hr
    simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hcs r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      h1.2.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine ⟨⟨hrd.trans h1.2.2.1, hwr.trans h1.2.2.2, hb, by rw [hcs _ (by decide), hsp], ?_⟩, r15_call h1 hcs,
    fun msg hm hpo => ?_⟩
  · have f1 : Frame ([⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩] ++ [below (s.gpr .rsp) 16]) s.mem s'.mem := by
      rw [← h1.1.2, ← hsp]; exact hf
    exact Frame.below_mono (a := 16) (b := 32) f1 (by omega_using []) (by omega_using [])
  · rw [← h1.1.2] at hm ⊢
    exact hR msg hm hpo

abbrev kpadArgs (rate pos suffix : Nat) : List (Reg × Arg) :=
  [(.rdi, .ptr (sc 0)), (.rsi, .imm rate), (.rdx, .imm pos), (.rcx, .imm suffix), (.r8, .ptr (sc 200))]

theorem postB_call {s s1 s' : State} {as : List (Reg × Arg)} (h1 : Args as s s1) {W : List Region}
    (hrd : s'.rd = s1.rd) (hwr : s'.wr = s1.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s1.gpr r)
    (hf : Frame (W ++ [below (s.gpr .rsp) 16]) s.mem s'.mem) : PostB s s' W := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  refine ⟨hrd.trans h1.2.2.1, hwr.trans h1.2.2.2, fun r hr => ?_, by rw [hcs _ (by decide), hsp],
    Frame.below_mono (a := 16) (b := 32) hf (by omega_using []) (by omega_using [])⟩
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hcs r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
    h1.2.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]

theorem kpad_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true)
    {pos : Nat} (hpos : pos < 136) :
    WP isa (kpad 136 pos 0x1f) s fun s' => PPostB s s' [(sc 0, 200), (sc 200, 640)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) 136 msg → pos = msg.length % 136 →
        stateAt s'.mem (pa s (sc 0)) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  obtain ⟨d1, k1, k2, w1, w2⟩ := kChk_spec L hk
  have hS := L.ok
  have c0 : inB (rbs ++ wbs) (sc 0) 200 = true := by
    simp only [kChk, Bool.and_eq_true] at hk; exact hk.1.1.1.2
  have c1 : inB (rbs ++ wbs) (sc 200) 640 = true := by
    simp only [kChk, Bool.and_eq_true] at hk; exact hk.1.1.2
  have ha : ∀ a ∈ kpadArgs 136 pos 0x1f, a.2.Ok ∧ a.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS c0, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩, ⟨show pos < 2 ^ 31 by omega_using [hpos], by decide⟩,
      ⟨show 0x1f < 2 ^ 31 by decide, by decide⟩, ⟨ptr_ok hS c1, by decide⟩⟩
  refine WP.seq (WP.mono (glue_ok' ha (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : Args (kpadArgs 136 pos 0x1f) s s1) => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  have kk : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 16).Disjoint R :=
    fun h => by rw [hsp]; exact h.sub_left (below_sub (by omega_using []) (by omega_using []))
  refine pad_call ⟨h1.r0, h1.r1, h1.r2, h1.r4, by decide, hpos, d1, kk k1, kk k2⟩
    (by rw [h1.2.2.1, h1.2.2.2]; exact Covers.append_left Covers.nil (Covers.right (Covers.cons w1 w2)))
    (by rw [h1.2.2.2]; exact Covers.cons w1 w2) (fun s' hrd hwr hcs hf hR => ⟨postB_call h1 hrd hwr hcs ?_, r15_call h1 hcs, ?_⟩)
  · rw [← h1.1.2, ← hsp]; exact hf
  · intro msg hm hpo
    rw [← h1.1.2] at hm
    have := hR msg hm hpo
    simp only [Arg.val] at this
    rw [this, h1.r3]
    rfl

abbrev ksqzArgs (rate : Nat) (dst : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.rdi, .ptr (sc 0)), (.rsi, .imm rate), (.rdx, .imm 0), (.rcx, .ptr dst), (.r8, .imm len), (.r9, .ptr (sc 200))]

theorem ksqz_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true)
    {out : Ptr} {len : Nat} (ho : outChk (rbs ++ wbs) wbs out len = true) :
    WP isa (ksqz 136 out len) s fun s' => PPostB s s' [(sc 0, 200), (out, len), (sc 200, 640)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s out) len = squeezeFrom 136 (stateAt s.mem (pa s (sc 0))) 0 len := by
  obtain ⟨d1, k1, k2, w1, w2⟩ := kChk_spec L hk
  simp only [outChk, Bool.and_eq_true] at ho
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, o4⟩ := ho
  have hS := L.ok
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec o3; have := (hS _ hn).1; omega
  have c0 : inB (rbs ++ wbs) (sc 0) 200 = true := by
    simp only [kChk, Bool.and_eq_true] at hk; exact hk.1.1.1.2
  have c1 : inB (rbs ++ wbs) (sc 200) 640 = true := by
    simp only [kChk, Bool.and_eq_true] at hk; exact hk.1.1.2
  have ha : ∀ a ∈ ksqzArgs 136 out len, a.2.Ok ∧ a.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS c0, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩, ⟨show 0 < 2 ^ 31 by decide, by decide⟩,
      ⟨ptr_ok hS o3, by decide⟩, ⟨hlen, by decide⟩, ⟨ptr_ok hS c1, by decide⟩⟩
  refine WP.seq (WP.mono (glue_ok' ha (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : Args (ksqzArgs 136 out len) s s1) => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  have kk : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 16).Disjoint R :=
    fun h => by rw [hsp]; exact h.sub_left (below_sub (by omega_using []) (by omega_using []))
  refine squeeze_call ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, by decide, by omega_using [hlen], (L.disj o1).symm, d1,
    L.disj o2, kk k1, kk (L.stkD o3), kk k2⟩
    (by rw [h1.2.2.1, h1.2.2.2]; exact Covers.append_left Covers.nil (Covers.right (Covers.cons w1 (Covers.cons (L.cW o4) w2))))
    (by rw [h1.2.2.2]; exact Covers.cons w1 (Covers.cons (L.cW o4) w2)) (fun s' hrd hwr hcs hf hR => ⟨postB_call h1 hrd hwr hcs ?_, r15_call h1 hcs, ?_⟩)
  · rw [← h1.1.2, ← hsp]; exact hf
  · simp only [Arg.val] at hR
    rw [hR, h1.1.2]

/-! ## The hash -/

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) : Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem hash2_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a b out : Ptr} {la lb len : Nat}
    (hc : hashChk (rbs ++ wbs) wbs a la b lb out len = true) :
    WP isa (hash2 a la b lb out len) s fun s' => PPostB s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s out) len = H (bytesAt s.mem (pa s a) la ++ bytesAt s.mem (pa s b) lb) len := by
  simp only [hashChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, pa'⟩, pb⟩, ho⟩, ka⟩, kb⟩, kb'⟩, hla⟩, hla0⟩ := hc
  obtain ⟨_, _, _, w0, _⟩ := kChk_spec L hk
  unfold hash2
  refine WP.seq (WP.mono (kzero_ok s w0) fun s₁ ⟨hP₁, f₁, hz⟩ => ?_)
  have L₁ := L.post hP₁
  have e1 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
  refine WP.seq (WP.mono (kabs_ok L₁ hk pa' (pos := 0) (by decide)) fun s₂ ⟨hP₂, f₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂
  have e2 : pa s₂ (sc 0) = pa s₁ (sc 0) := hP₂.pa (by decide)
  have hR₂' := hR₂ [] (by rw [e1]; exact repr_nil hz) rfl
  rw [List.nil_append, L.keepBytes hP₁ ka] at hR₂'
  refine WP.seq (WP.mono (kabs_ok L₂ hk pb (pos := la % 136) (Nat.mod_lt _ (by decide))) fun s₃ ⟨hP₃, f₃, hR₃⟩ => ?_)
  have L₃ := L₂.post hP₃
  have e3 : pa s₃ (sc 0) = pa s₂ (sc 0) := hP₃.pa (by decide)
  have hR₃' := hR₃ _ (by rw [e2]; exact hR₂') (by rw [Proof.MlKem.bytesAt_length])
  rw [L₁.keepBytes hP₂ kb', L.keepBytes hP₁ kb] at hR₃'
  refine WP.seq (WP.mono (kpad_ok L₃ hk (pos := (la + lb) % 136) (Nat.mod_lt _ (by decide))) fun s₄ ⟨hP₄, f₄, hS₄⟩ => ?_)
  have L₄ := L₃.post hP₄
  have e4 : pa s₄ (sc 0) = pa s₃ (sc 0) := hP₄.pa (by decide)
  have hS := hS₄ _ (by rw [e3]; exact hR₃') (by rw [List.length_append, Proof.MlKem.bytesAt_length,
    Proof.MlKem.bytesAt_length])
  have hob : out.1 ∈ bases := by
    simp only [outChk, Bool.and_eq_true] at ho; exact ptr_bs L.ok ho.1.2
  have eo : pa s₄ out = pa s out := by rw [hP₄.pa hob, hP₃.pa hob, hP₂.pa hob, hP₁.pa hob]
  refine WP.mono (ksqz_ok L₄ hk ho) fun s₅ ⟨hP₅, f₅, h₅⟩ => ⟨?_, by rw [f₅, f₄, f₃, f₂, f₁], ?_⟩
  · refine PPostB.trans (PPostB.trans (PPostB.trans (PPostB.trans hP₁ hP₂ (ws := [(sc 0, 200), (sc 200, 640)])
      (by decide) (by simp) (by simp)) hP₃ (by decide) (fun w hw => hw) (fun w hw => hw)) hP₄ (by decide)
      (fun w hw => hw) (fun w hw => hw)) hP₅ ?_ (by simp) (by simp)
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨by decide, hob, by decide⟩
  · rw [← eo, h₅, e4, hS, squeezeFrom_zero]
    rfl

end VG.Proof.MlDsa.X86_64.Verify

end

end

/-!
# ML-DSA verification on x86-64: the sponge leaks only addresses

Two runs in the same layout (`LRel`: layouts whose registers and stack pointer
agree) stay in it across code that keeps the layout (`LRel.step`), and `hash2`
leaks the same in both (`hash2_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates Repr squeezeFrom)

/-- Two runs in the layout, with the same layout registers and stack pointer. -/
def LRel (rbs wbs : List (Reg × Nat)) (x y : State) : Prop := Lay rbs wbs x ∧ Lay rbs wbs y ∧ SameB x y

theorem SameB.post {x y x' y' : State} {W₁ W₂ : List Region} (h : SameB x y) (hx : PostB x x' W₁)
    (hy : PostB y y' W₂) : SameB x' y' :=
  ⟨fun r hr => by rw [hx.bs r hr, hy.bs r hr, h.1 r hr], by rw [hx.rsp, hy.rsp, h.2]⟩

theorem LRel.post {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region} (h : LRel rbs wbs x y)
    (hx : PostB x x' W₁) (hy : PostB y y' W₂) : LRel rbs wbs x' y' :=
  ⟨h.1.post hx, h.2.1.post hy, h.2.2.post hx hy⟩

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem LRel.step {rbs wbs : List (Reg × Nat)} {c : Prog isa}
    (htr : RelCT isa (LRel rbs wbs) c fun _ _ => True)
    (hok : ∀ x, Lay rbs wbs x → WP isa c x fun x' => ∃ W, PostB x x' W) :
    RelCT isa (LRel rbs wbs) c (LRel rbs wbs) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB x x' W) (fun x y h => ⟨hok x h.1, hok y h.2.1⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  RelCT.postDep (block_nomem_tr fun _ hi => absurd hi List.not_mem_nil) (F := fun x x' => x' = x)
    (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (by taint_decide)

/-! ## The calls -/

theorem k_in {bs wbs : List (Reg × Nat)} (hk : kChk bs wbs = true) :
    inB bs (sc 0) 200 = true ∧ inB bs (sc 200) 640 = true := by
  simp only [kChk, Bool.and_eq_true] at hk; exact ⟨hk.1.1.1.2, hk.1.1.2⟩

theorem kk16 {s s1 : State} (hsp : s1.gpr .rsp = s.gpr .rsp) {R : Region} (h : (below (s.gpr .rsp) 32).Disjoint R) :
    (below (s1.gpr .rsp) 16).Disjoint R := by
  rw [hsp]; exact h.sub_left (below_sub (by omega_using []) (by omega_using []))

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true)
include L hk

theorem kabs_args {src : Ptr} {len pos : Nat} (hp : pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136)
    {s1 : State} (h1 : Args (kabsArgs src len 136 pos) s s1) :
    AbsorbArgs s1 (pa s (sc 0)) (pa s src) (pa s (sc 200)) 136 pos len := by
  obtain ⟨d1, k1, k2, _, _⟩ := kChk_spec L hk
  simp only [pieceChk, Bool.and_eq_true] at hp
  obtain ⟨⟨p1, p2⟩, p3⟩ := hp
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec p3; have := (L.ok _ hn).1; omega
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, hpos, by omega_using [hlen], d1, L.disj p1, L.disj p2,
    kk16 h1.rsp k1, kk16 h1.rsp (L.stkD p3), kk16 h1.rsp k2⟩

theorem kpad_args {pos : Nat} (hpos : pos < 136) {s1 : State} (h1 : Args (kpadArgs 136 pos 0x1f) s s1) :
    PadArgs s1 (pa s (sc 0)) (pa s (sc 200)) 136 pos := by
  obtain ⟨d1, k1, k2, _, _⟩ := kChk_spec L hk
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r4, by decide, hpos, d1, kk16 h1.rsp k1, kk16 h1.rsp k2⟩

theorem ksqz_args {out : Ptr} {len : Nat} (ho : outChk (rbs ++ wbs) wbs out len = true) {s1 : State}
    (h1 : Args (ksqzArgs 136 out len) s s1) :
    SqueezeArgs s1 (pa s (sc 0)) (pa s out) (pa s (sc 200)) 136 0 len := by
  obtain ⟨d1, k1, k2, _, _⟩ := kChk_spec L hk
  simp only [outChk, Bool.and_eq_true] at ho
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, _⟩ := ho
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec o3; have := (L.ok _ hn).1; omega
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, by decide, by omega_using [hlen], (L.disj o1).symm, d1,
    L.disj o2, kk16 h1.rsp k1, kk16 h1.rsp (L.stkD o3), kk16 h1.rsp k2⟩

end


/-- A pointer's value agrees in two runs in the same layout. -/
theorem LRel.val {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel rbs wbs x y) {p : Ptr} {l : Nat}
    (hin : inB (rbs ++ wbs) p l = true) : (Arg.ptr p).val x = (Arg.ptr p).val y :=
  h.2.2.pa (ptr_bs h.1.ok hin)

theorem kabs_aok {bs wbs : List (Reg × Nat)} (hS : LayOk bs) (hk : kChk bs wbs = true) {src : Ptr} {len pos : Nat}
    (hp : pieceChk bs src len = true) (hpos : pos < 136) : ∀ a ∈ kabsArgs src len 136 pos, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [pieceChk, Bool.and_eq_true] at hp
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec hp.2; have := (hS _ hn).1; omega
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok hS (k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show pos < 2 ^ 31 by omega_using [hpos], by decide⟩, ⟨ptr_ok hS hp.2, by decide⟩, ⟨hlen, by decide⟩,
    ⟨ptr_ok hS (k_in hk).2, by decide⟩⟩

theorem kpad_aok {bs wbs : List (Reg × Nat)} (hS : LayOk bs) (hk : kChk bs wbs = true) {pos : Nat} (hpos : pos < 136) :
    ∀ a ∈ kpadArgs 136 pos 0x1f, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok hS (k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show pos < 2 ^ 31 by omega_using [hpos], by decide⟩, ⟨show 0x1f < 2 ^ 31 by decide, by decide⟩,
    ⟨ptr_ok hS (k_in hk).2, by decide⟩⟩

theorem ksqz_aok {bs wbs : List (Reg × Nat)} (hS : LayOk bs) (hk : kChk bs wbs = true) {out : Ptr} {len : Nat}
    (ho : outChk bs wbs out len = true) : ∀ a ∈ ksqzArgs 136 out len, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [outChk, Bool.and_eq_true] at ho
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec ho.1.2; have := (hS _ hn).1; omega
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok hS (k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show 0 < 2 ^ 31 by decide, by decide⟩, ⟨ptr_ok hS ho.1.2, by decide⟩, ⟨hlen, by decide⟩,
    ⟨ptr_ok hS (k_in hk).2, by decide⟩⟩

theorem kabs_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) (hk : kChk (rbs ++ wbs) wbs = true) {src : Ptr} {len pos : Nat}
    (hp : pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136) :
    RelCT isa (LRel rbs wbs) (kabs src len 136 pos) fun _ _ => True := by
  have hp' := hp
  simp only [pieceChk, Bool.and_eq_true] at hp'
  have p3 := hp'.2
  refine callAt_tr (k := Proof.Sha3.absorbX86_64) Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (kabs_aok hS hk hp hpos)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  · obtain ⟨_, _, _, w1, w2⟩ := kChk_spec h.1 hk
    obtain ⟨_, _, _, w1', w2'⟩ := kChk_spec h.2.1 hk
    refine ⟨_, _, _, _, absorb_pre (kabs_args h.1 hk hp hpos h1), absorb_pre (kabs_args h.2.1 hk hp hpos h2), ?_,
      Covers.append_left (h.1.cR p3) (Covers.right (Covers.cons w1 w2)), Covers.cons w1 w2,
      Covers.append_left (h.2.1.cR p3) (Covers.right (Covers.cons w1' w2')), Covers.cons w1' w2', h.2.2.2⟩
    simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]
    rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h2.r5, h1.rsp, h2.rsp,
      h.val (k_in hk).1, h.val (k_in hk).2, h.val p3, h.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem kpad_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) (hk : kChk (rbs ++ wbs) wbs = true) {pos : Nat}
    (hpos : pos < 136) : RelCT isa (LRel rbs wbs) (kpad 136 pos 0x1f) fun _ _ => True := by
  refine callAt_tr (k := Proof.Sha3.padX86_64) Proof.Sha3.X86_64.Stream.Pad.pad_correct
    Proof.Sha3.X86_64.Stream.Pad.pad_ct (kpad_aok hS hk hpos)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  obtain ⟨_, _, _, w1, w2⟩ := kChk_spec h.1 hk
  obtain ⟨_, _, _, w1', w2'⟩ := kChk_spec h.2.1 hk
  refine ⟨_, _, _, _, pad_pre (kpad_args h.1 hk hpos h1), pad_pre (kpad_args h.2.1 hk hpos h2), ?_,
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1 w2)), Covers.cons w1 w2,
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1' w2')), Covers.cons w1' w2', h.2.2.2⟩
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide)]
  rw [h1.r0, h1.r1, h1.r2, h1.r4, h2.r0, h2.r1, h2.r2, h2.r4, h1.rsp, h2.rsp,
    h.val (k_in hk).1, h.val (k_in hk).2, h.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ksqz_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) (hk : kChk (rbs ++ wbs) wbs = true)
    {out : Ptr} {len : Nat} (ho : outChk (rbs ++ wbs) wbs out len = true) :
    RelCT isa (LRel rbs wbs) (ksqz 136 out len) fun _ _ => True := by
  have ho' := ho
  simp only [outChk, Bool.and_eq_true] at ho'
  obtain ⟨⟨⟨_, _⟩, o3⟩, o4⟩ := ho'
  refine callAt_tr (k := Proof.Sha3.squeezeX86_64) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (ksqz_aok hS hk ho)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  obtain ⟨_, _, _, w1, w2⟩ := kChk_spec h.1 hk
  obtain ⟨_, _, _, w1', w2'⟩ := kChk_spec h.2.1 hk
  refine ⟨_, _, _, _, squeeze_pre (ksqz_args h.1 hk ho h1), squeeze_pre (ksqz_args h.2.1 hk ho h2), ?_,
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1 (Covers.cons (h.1.cW o4) w2))),
    Covers.cons w1 (Covers.cons (h.1.cW o4) w2),
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1' (Covers.cons (h.2.1.cW o4) w2'))),
    Covers.cons w1' (Covers.cons (h.2.1.cW o4) w2'), h.2.2.2⟩
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h2.r5, h1.rsp, h2.rsp,
    h.val (k_in hk).1, h.val (k_in hk).2, h.val o3, h.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hash2_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {a b out : Ptr} {la lb len : Nat}
    (hc : hashChk (rbs ++ wbs) wbs a la b lb out len = true) :
    RelCT isa (LRel rbs wbs) (hash2 a la b lb out len) fun _ _ => True := by
  have hc' := hc
  simp only [hashChk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, pa'⟩, pb⟩, ho⟩, _⟩, _⟩, _⟩, hla⟩, _⟩ := hc'
  unfold hash2
  refine RelCT.seq (LRel.step (kzero_tr fun x y h => h.2.2.1 _ (by decide))
    fun x Lx => WP.mono (kzero_ok x (kChk_spec Lx hk).2.2.2.1) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kabs_tr hS hk pa' (by decide))
    fun x Lx => WP.mono (kabs_ok Lx hk pa' (by decide)) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kabs_tr hS hk pb (Nat.mod_lt _ (by decide)))
    fun x Lx => WP.mono (kabs_ok Lx hk pb (Nat.mod_lt _ (by decide))) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kpad_tr hS hk (Nat.mod_lt _ (by decide)))
    fun x Lx => WP.mono (kpad_ok Lx hk (Nat.mod_lt _ (by decide))) fun _ h => ⟨_, h.1⟩) ?_
  exact ksqz_tr hS hk ho

end VG.Proof.MlDsa.X86_64.Verify
