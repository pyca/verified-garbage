module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `MlKem.X86_64.FragS`, which the modules that import this one used -/

section

/-! ### `MlKem.X86_64.FragL`, which this module and modules that import it used -/

section

/-!
# ML-KEM-768 on x86-64: the calls of the polynomial primitives, in a layout

Each call of a primitive from a state in a layout whose pointers pass its
check: what it leaves (`PPost`) and computes (`addAt_ok`, …), and that two
runs in the layout leak the same (`addAt_tr`, …).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt rates)

section
variable {rbs wbs : List (Reg × Nat)}

theorem rdOk_in {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : rdOk bs p l = true) : inB bs p l = true := by
  simp only [rdOk, Bool.and_eq_true] at h; exact h.2

theorem wrOk_in {bs wbs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : wrOk bs wbs p l = true) : inB bs p l = true := by
  simp only [wrOk, Bool.and_eq_true] at h; exact rdOk_in h.1

/-! ## Addition and subtraction -/

theorem accChk_in {bs wbs : List (Reg × Nat)} {f g : Ptr} (hc : accChk bs wbs f g = true) :
    inB bs f 1024 = true ∧ inB bs g 1024 = true := by
  simp only [accChk, Bool.and_eq_true] at hc; exact ⟨wrOk_in hc.1.1, rdOk_in hc.1.2⟩

theorem addAt_ok {A : Arith} (hA : ArithOk A) {s : State} (L : Lay rbs wbs s) {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (addAt A f g) s fun s' => PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (pa s f) (add (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok hA.add.ok hA.add.nosp (by rw [hA.add.depth]; decide) (fun e => hg (by rw [e]; decide)) (AccH.of L hc rf rg)

theorem subAt_ok {A : Arith} (hA : ArithOk A) {s : State} (L : Lay rbs wbs s) {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (pa s f)) (rg : Reduced s.mem (pa s g)) :
    WP isa (subAt A f g) s fun s' => PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (pa s f) (sub (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) :=
  accAt_ok hA.sub.ok hA.sub.nosp (by rw [hA.sub.depth]; decide) (fun e => hg (by rw [e]; decide)) (AccH.of L hc rf rg)

theorem addAt_tr {A : Arith} (hA : ArithOk A) {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (addAt A f g) fun _ _ => True :=
  RelCT.mono (accAt_tr hA.add.ok hA.add.ct (fun e => hg (by rw [e]; decide)))
    (fun _ _ ⟨h, ⟨r1, r2⟩, r3, r4⟩ => ⟨AccH.of h.1 hc r1 r2, AccH.of h.2.1 hc r3 r4, h.eq (accChk_in hc).1,
      h.eq (accChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

theorem subAt_tr {A : Arith} (hA : ArithOk A) {f g : Ptr} (hg : NA g) (hc : accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g))) (subAt A f g) fun _ _ => True :=
  RelCT.mono (accAt_tr hA.sub.ok hA.sub.ct (fun e => hg (by rw [e]; decide)))
    (fun _ _ ⟨h, ⟨r1, r2⟩, r3, r4⟩ => ⟨AccH.of h.1 hc r1 r2, AccH.of h.2.1 hc r3 r4, h.eq (accChk_in hc).1,
      h.eq (accChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

/-! ## Two pointers: `SamplePolyCBD₂`, `ByteEncode₁₂`, `ByteDecode₁₂` and the compressions -/

theorem twoChk_in {bs wbs : List (Reg × Nat)} {p q : Ptr} {n m : Nat} (hc : twoChk bs wbs p n q m = true) :
    inB bs p n = true ∧ inB bs q m = true := by
  simp only [twoChk, Bool.and_eq_true] at hc; exact ⟨rdOk_in hc.1.1, wrOk_in hc.1.2⟩

theorem cbd2At_okL {A : Arith} (hA : ArithOk A) {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 128 q 1024 = true) :
    WP isa (cbd2At A p q) s fun s' => PPost s s' [(q, 1024)] ∧
      PolyIs s'.mem (pa s q) (samplePolyCBD 2 (bytesAt s.mem (pa s p) 128)) :=
  cbd2At_ok hA hq (TwoH.of L hc)

theorem cbd2At_trL {A : Arith} (hA : ArithOk A) {p q : Ptr} (hq : NA q) (hc : twoChk (rbs ++ wbs) wbs p 128 q 1024 = true) :
    RelCT isa (LRel rbs wbs) (cbd2At A p q) fun _ _ => True :=
  RelCT.mono (cbd2At_tr hA hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem enc12At_okL {A : Arith} (hA : ArithOk A) {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 1024 q 384 = true) (red : Reduced s.mem (pa s p)) :
    WP isa (enc12At A p q) s fun s' => PPost s s' [(q, 384)] ∧
      bytesAt s'.mem (pa s q) 384 = encode12 (polyAt s.mem (pa s p)) :=
  enc12At_ok hA hq (TwoH.of L hc) red

theorem enc12At_trL {A : Arith} (hA : ArithOk A) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 1024 q 384 = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Reduced x.mem (pa x p) ∧ Reduced y.mem (pa y p)) (enc12At A p q)
      fun _ _ => True :=
  RelCT.mono (enc12At_tr hA hq) (fun _ _ ⟨e, r1, r2⟩ => ⟨⟨TwoH.of e.1 hc, r1⟩, ⟨TwoH.of e.2.1 hc, r2⟩,
    e.eq (twoChk_in hc).1, e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem dec12At_okL {A : Arith} (hA : ArithOk A) {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 384 q 1024 = true) :
    WP isa (dec12At A p q) s fun s' => PPost s s' [(q, 1024)] ∧
      PolyIs s'.mem (pa s q) (decode12 (bytesAt s.mem (pa s p) 384)) :=
  dec12At_ok hA hq (TwoH.of L hc)

theorem dec12At_trL {A : Arith} (hA : ArithOk A) {p q : Ptr} (hq : NA q) (hc : twoChk (rbs ++ wbs) wbs p 384 q 1024 = true) :
    RelCT isa (LRel rbs wbs) (dec12At A p q) fun _ _ => True :=
  RelCT.mono (dec12At_tr hA hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem ceCall_okL {n : String} {c : Prog isa} {ws : List Nat} (I : CEImpl n c ws) {s : State} (L : Lay rbs wbs s)
    {f out : Ptr} {d : Nat} (hout : NA out) (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true) (hd : d ∈ ws)
    (red : Reduced s.mem (pa s f)) :
    WP isa (ceCall n c f d out) s fun s' => PPost s s' [(out, 32 * d)] ∧
      bytesAt s'.mem (pa s out) (32 * d) = compressEncode d (polyAt s.mem (pa s f)) :=
  ceCall_ok I hout (CEH.of L hc hd red)

theorem ceCall_trL {n : String} {c : Prog isa} {ws : List Nat} (I : CEImpl n c ws) {f out : Ptr} {d : Nat}
    (hout : NA out) (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true) (hd : d ∈ ws) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f)) (ceCall n c f d out)
      fun _ _ => True :=
  RelCT.mono (ceCall_tr I hout) (fun _ _ ⟨e, r1, r2⟩ => ⟨CEH.of e.1 hc hd r1, CEH.of e.2.1 hc hd r2,
    e.eq (twoChk_in hc).1, e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem ddCall_okL {n : String} {c : Prog isa} {ws : List Nat} (I : DDImpl n c ws) {s : State} (L : Lay rbs wbs s)
    {b f : Ptr} {d : Nat} (hf : NA f) (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true) (hd : d ∈ ws) :
    WP isa (ddCall n c b d f) s fun s' => PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (pa s f) (decodeDecompress d (bytesAt s.mem (pa s b) (32 * d))) :=
  ddCall_ok I hf (DDH.of L hc hd)

theorem ddCall_trL {n : String} {c : Prog isa} {ws : List Nat} (I : DDImpl n c ws) {b f : Ptr} {d : Nat} (hf : NA f)
    (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true) (hd : d ∈ ws) :
    RelCT isa (LRel rbs wbs) (ddCall n c b d f) fun _ _ => True :=
  RelCT.mono (ddCall_tr I hf) (fun _ _ e => ⟨DDH.of e.1 hc hd, DDH.of e.2.1 hc hd, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

/-! ## `SampleNTT` -/

theorem sampChk_in {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : sampChk bs wbs a = true) :
    inB bs (sc oSB) 34 = true ∧ inB bs a 1024 = true := by
  simp only [sampChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨rdOk_in h1, wrOk_in h2⟩

theorem sampleAt_trL {a : Ptr} (hna : NA a) (hc : sampChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34)
      (sampleAt a) fun _ _ => True :=
  RelCT.mono (sampleAt_tr hna) (fun _ _ ⟨e, hb⟩ => ⟨SampH.of e.1 hc, SampH.of e.2.1 hc,
    e.eq (sampChk_in hc).1, e.eq (sampChk_in hc).2, e.2.2.2, hb⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM-768 on x86-64: byte stores, copies, and the calls of `SampleNTT`

In a layout: a byte store (`setB_okL`), a copy (`copy_okL`), and the entry
`Â[i, j]` of the matrix, `SampleNTT(ρ ‖ j ‖ i)` with `ρ` at `SB`
(`sampleIJ_ok`, `sampleIJ_tr`), which changes `r15` (so what it leaves is
`PostB`, not `Post`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem rbx_cs : Reg.rbx ∈ calleeSaved := by decide
theorem rbx_na : Reg.rbx ∉ argRegs := by decide
theorem rbx_bases : Reg.rbx ∈ bases := by decide

/-! ## Composing what pieces leave -/

theorem PPostB.app {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : PPostB s s₁ ws₁) (h₂ : PPostB s₁ s₂ ws₂)
    (hb : ∀ w ∈ ws₂, w.1.1 ∈ bases) : PPostB s s₂ (ws₁ ++ ws₂) := by
  have e : ws₂.map (toR s₁) = ws₂.map (toR s) := List.map_congr_left fun w hw => by simp only [toR, h₁.pa (hb w hw)]
  have f₂ := h₂.frame
  rw [e, h₁.rsp] at f₂
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr), h₂.rsp.trans h₁.rsp,
    (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (by rw [List.map_append]; exact List.mem_append_left _ hr)
    · exact List.mem_append_right _ hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (by rw [List.map_append]; exact List.mem_append_right _ hr)
    · exact List.mem_append_right _ hr

theorem PPost.app {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : PPost s s₁ ws₁) (h₂ : PPost s₁ s₂ ws₂)
    (hcs : ∀ w ∈ ws₂, w.1.1 ∈ calleeSaved) : PPost s s₂ (ws₁ ++ ws₂) :=
  PPost.trans h₁ h₂ hcs (fun _ hw => List.mem_append_left _ hw) (fun _ hw => List.mem_append_right _ hw)

/-! ## A byte -/

section
variable {rbs wbs : List (Reg × Nat)}

theorem bytesAt_one (m : Mem) (a : Addr) : bytesAt m a 1 = [m a] := by
  simp [bytesAt]

theorem setB_okL {s : State} (L : Lay rbs wbs s) {p : Ptr} {v : Nat} (hr : p.1 ≠ .rax) (hv : v < 256)
    (hc : inB wbs p 1 = true) :
    WP isa (.block (setB p v)) s fun s' => PPost s s' [(p, 1)] ∧ bytesAt s'.mem (pa s p) 1 = [BitVec.ofNat 8 v] := by
  have hw : InRegions s.wr (pa s p) 1 := L.cW hc _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (setB_ok p v hr hv s hw) fun s' ⟨hm, k⟩ => ⟨post_of_keep k (by decide) ?_, ?_⟩
  · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [hm, bytesAt_one, writeW8_apply, ifp rfl]

/-! ## A copy -/

def copyChk (bs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  wrOk bs wbs dst n && rdOk bs src n && sepB bs src n dst n && decide (0 < n) && decide (n % 8 = 0) &&
    decide (n < 2 ^ 31)

theorem copy_okL {s : State} (L : Lay rbs wbs s) {dst src : Ptr} {n : Nat} (hsr : src.1 ≠ .rdi)
    (hc : copyChk (rbs ++ wbs) wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => PPost s s' [(dst, n)] ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n := by
  simp only [copyChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hod, hid⟩, hwd⟩, hos, his⟩, hs⟩, hn0⟩, h8⟩, hn⟩ := hc
  have hrd : InRegions (s.rd ++ s.wr) (pa s src) n := L.cR his _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hwr : InRegions s.wr (pa s dst) n := L.cW hwd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  exact WP.mono (copy_ok dst src n hn0 h8 hn hod hos hsr s hrd hwr (L.disj hs))
    fun s' ⟨hb, hf, k⟩ => ⟨post_of_keep k (by decide) hf, hb⟩

end

/-! ## The seed of `SampleNTT` -/

/-- What `SampleNTT` leaves, as `PostB`. -/
theorem SampPost.b {a : Ptr} {s s' : State} (h : SampPost a s s') :
    PPostB s s' [(a, 1024), (sc oSS, 2048)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

/-- The checks of `Â[i, j]`: its call, and the two bytes of the seed. -/
def ijChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  sampChk bs wbs a && inB wbs (sc (oSB + 32)) 1 && inB wbs (sc (oSB + 33)) 1 &&
    keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 && keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 &&
    keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1

theorem ijChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : ijChk bs wbs a = true) :
    sampChk bs wbs a = true ∧ inB wbs (sc (oSB + 32)) 1 = true ∧ inB wbs (sc (oSB + 33)) 1 = true ∧
      keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 = true ∧ keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 = true ∧
      keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1 = true := by
  simp only [ijChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The two indices of the seed `ρ ‖ j ‖ i`. -/
theorem setIJ_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat} (hi : i < 256) (hj : j < 256) {a : Ptr}
    (hc : ijChk (rbs ++ wbs) wbs a = true) :
    WP isa (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) s fun s' =>
      PPost s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt s'.mem (pa s' (sc oSB)) 34 = matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j := by
  obtain ⟨_, h32, h33, k1, k2, k3⟩ := ijChk_spec hc
  rw [WP.block_append_iff]
  refine WP.mono (setB_okL L (by decide) hj h32) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (setB_okL L₁ (by decide) hi h33) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have e1 : ∀ o, pa s₁ (sc o) = pa s (sc o) := fun o => hP₁.pa rbx_cs
  have e2 : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun o => hP₂.pa rbx_cs
  have hρ : bytesAt s₂.mem (pa s₂ (sc oSB)) 32 = bytesAt s.mem (pa s (sc oSB)) 32 := by
    rw [L₁.keepBytes hP₂.b k2, L.keepBytes hP₁.b k1]
  have hjb : bytesAt s₂.mem (pa s₂ (sc (oSB + 32))) 1 = [BitVec.ofNat 8 j] := by
    rw [L₁.keepBytes hP₂.b k3, e1]; exact hb₁
  have hib : bytesAt s₂.mem (pa s₂ (sc (oSB + 33))) 1 = [BitVec.ofNat 8 i] := by
    rw [e2]; exact hb₂
  refine ⟨PPost.app hP₁ hP₂ (by decide), seed_eq hρ ?_ ?_⟩
  · refine mem_of_bytesAt_one ?_; rw [← hjb, pa, pa, off_add]
  · refine mem_of_bytesAt_one ?_; rw [← hib, pa, pa, off_add]

theorem sampleIJ_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {a : Ptr} (hna : NA a) {i j : Nat} (hi : i < 256)
    (hj : j < 256) (hc : ijChk (rbs ++ wbs) wbs a = true) :
    WP isa (sampleIJ a i j) s fun s' =>
      PPostB s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(a, 1024), (sc oSS, 2048)]) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j)).isSome then 1 else 0)) ∧
      ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j) = some f →
        PolyIs s'.mem (pa s a) f := by
  unfold sampleIJ
  rw [WP.seq_iff]
  refine WP.mono (setIJ_ok L hcs hi hj hc) fun s₂ ⟨hP₂, hseed⟩ => ?_
  have L₂ := L.post hP₂.b hcs
  refine WP.mono (sampleAt_ok hna (SampH.of L₂ (ijChk_spec hc).1)) fun s₃ h => ?_
  have hab : a.1 ∈ bases := by
    obtain ⟨n, hn, _⟩ := inB_spec (sampChk_in (ijChk_spec hc).1).2
    exact hcs (a.1, n) hn
  have e3 : pa s₂ a = pa s a := hP₂.b.pa hab
  refine ⟨PPostB.app hP₂.b h.b (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hab, by decide]), ?_, fun f hf => ?_⟩
  · rw [h.r15, hseed, hP₂.cs .r15 (by decide)]
  · rw [← e3]; exact h.res f (by rw [hseed]; exact hf)

theorem sampleIJ_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {a : Ptr} (hna : NA a)
    {i j : Nat} (hi : i < 256) (hj : j < 256) (hc : ijChk (rbs ++ wbs) wbs a = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i))
      (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 32 = bytesAt y.mem (pa y (sc oSB)) 32)
      (sampleIJ a i j) fun _ _ => True := by
  have hin : inB (rbs ++ wbs) (sc oSB) 34 = true := (sampChk_in (ijChk_spec hc).1).1
  unfold sampleIJ
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.eq hin) ht)
    (F := fun x x' => PPost x x' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt x'.mem (pa x' (sc oSB)) 34 = matSeed (bytesAt x.mem (pa x (sc oSB)) 32) i j)
    (fun x y h => ⟨setIJ_ok h.1.1 hcs hi hj hc, setIJ_ok h.1.2.1 hcs hi hj hc⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, by rw [hx.2, hy.2, h.2]⟩)
    (sampleAt_trL hna (ijChk_spec hc).1)

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: the input of `PRF`, and sequences in a layout

In a layout: the input of `PRF₂(σ, N)` (`prf_pieces`, for `Prfs.lean`), and
two pieces of code in sequence, for constant time (`RelCT.seqL`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem keepB_sub {bs : List (Reg × Nat)} {ws ws' : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (h : keepB bs ws p l = true) (hs : ∀ w ∈ ws', w ∈ ws) : keepB bs ws' p l = true := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun w hw => h.2 w (hs w hw)⟩

/-! ## `PRF₂(σ, N)` -/

theorem shake31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The bytes absorbed: `σ ‖ N`. -/
theorem prf_pieces {s : State} {N : Nat} (hN : bytesAt s.mem (pa s (sc oNB)) 1 = [BitVec.ofNat 8 N]) :
    pieces s [(sigP, 32), (sc oNB, 1)] = bytesAt s.mem (pa s sigP) 32 ++ [BitVec.ofNat 8 N] := by
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hN]

/-! ## Sequences, for constant time -/

/-- Two pieces of code in sequence, from two runs in a layout that satisfy
`I` (what the first piece needs), each piece leaving the layout. -/
theorem RelCT.seqL {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c₁ c₂ : Prog isa}
    {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, Lay rbs wbs x → I x → WP isa c₁ x fun x' => (∃ W, PostB x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => LRel rbs wbs x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.postDep h₁ (F := fun x x' => (∃ W, PostB x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.1 h.2.1, w₁ y h.1.2.1 h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hcs hx hy, jx, jy⟩) h₂

end VG.Proof.MlKem.X86_64
