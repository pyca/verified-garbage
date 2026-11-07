module
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Top
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Sha3.X86_64.Round


/-!
# ML-DSA signing on x86-64: what holds of the state between the pieces

The inputs of the function entered in `σ` (`skOf`, `muOf`, `rndOf`); what
holds of every state of it (`St`: `Top`, the layout, and the inputs where they
were), kept by each piece that writes only where `stChk` allows (`St.step`);
and polynomials in slots of the working space (`Pl`), in families of
consecutive slots (`Fam`), kept by pieces that write apart from them
(`Fam.keep`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Parts of buffers -/

theorem inB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} (h : inB bs (r, o) L = true)
    (h2 : o' + l ≤ o + L) : inB bs (r, o') l = true := by
  unfold inB at h ⊢
  split at h
  · rename_i n hn
    simp only [hn, decide_eq_true_eq] at h ⊢
    omega
  · cases h

theorem sepB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} {q : Ptr} {k : Nat}
    (h : sepB bs (r, o) L q k = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : sepB bs (r, o') l q k = true := by
  unfold sepB at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hp, hq⟩, hs⟩ := h
  refine ⟨⟨inB_sub hp h2, hq⟩, ?_⟩
  rcases hs with hs | ⟨he, hs⟩
  · exact .inl hs
  · exact .inr ⟨he, by omega⟩

theorem keepB_sub {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {r : Reg} {o L o' l : Nat} (h : keepB bs ws (r, o) L = true)
    (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : keepB bs ws (r, o') l = true := by
  unfold keepB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨h.1.1, inB_sub h.1.2 h2⟩, fun w hw => sepB_sub (h.2 w hw) h1 h2⟩

/-! ## The inputs -/

section
variable (p : Params)

/-- `sk`, `μ` and `rnd`, in the state `σ` the function is entered in. -/
abbrev skOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) p.skLen
abbrev muOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 64
abbrev rndOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) 32

end

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## Every state -/

/-- What holds of every state of the function entered in `σ`. -/
structure St (p : Params) (D : Nat) (σ s : State) : Prop where
  top : Top σ s
  lay : Lay D (sgR p) (sgW p) s
  sk : bytesAt s.mem (pa s (.rbp, 0)) p.skLen = skOf p σ
  mu : bytesAt s.mem (pa s (.r12, 0)) 64 = muOf σ
  rnd : bytesAt s.mem (pa s (.r13, 0)) 32 = rndOf σ
  /-- Memory changed only where the function may write: its writable buffers and its stack. -/
  fr : Frame (σ.wr ++ [below (σ.gpr .rsp) D]) σ.mem s.mem

/-- A piece that writes `ws` keeps `St`. -/
def stChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  topChk (sgB p) ws && keepB (sgB p) ws (.rbp, 0) p.skLen && keepB (sgB p) ws (.r12, 0) 64 &&
    keepB (sgB p) ws (.r13, 0) 32 && ws.all (fun w => inB (sgW p) w.1 w.2)

theorem sub_of_contains {r : Region} {a : Addr} {n : Nat} (h : r.Contains a n) (hn : n < 2 ^ 64) :
    Region.Sub ⟨a, n⟩ r := fun x hx => by
  have hx' : (x - a).toNat + 1 ≤ n := hx
  have e : x = a + BitVec.ofNat 64 (x - a).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [e]
  exact VG.CallLay.contains_trans h hx' hn

/-- A frame of the regions `ws` of the writable buffers, within the frame of
the writable regions and the stack. -/
theorem frame_ws {D : Nat} {rbs wbs : List (Reg × Nat)} {σ s s' : State} (L : Lay D rbs wbs s)
    (hwr : s.wr = σ.wr) (hsp : s.gpr .rsp = σ.gpr .rsp) {ws : List (Ptr × Nat)}
    (hw : ws.all (fun w => inB wbs w.1 w.2) = true)
    (hf : Frame (ws.map (toR s) ++ [below (s.gpr .rsp) D]) s.mem s'.mem) :
    Frame (σ.wr ++ [below (σ.gpr .rsp) D]) s.mem s'.mem := by
  refine Frame.sub hf fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
    have hi := List.all_eq_true.mp hw w hw'
    obtain ⟨r', hr', hc⟩ := L.iW hi
    obtain ⟨n, hn, hl⟩ := inB_spec hi
    have := L.small _ (List.mem_append_right _ hn)
    exact ⟨r', List.mem_append_left _ (hwr ▸ hr'), sub_of_contains hc (by omega)⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by rw [hsp]; exact fun _ h => h⟩

theorem St.step {p : Params} {D : Nat} {σ s s' : State} (h : St p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : stChk p ws = true) : St p D σ s' := by
  simp only [stChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  exact ⟨h.top.step h.lay hP h1, h.lay.post hP (sgB_bases p), (h.lay.keepBytes hP h2).trans h.sk,
    (h.lay.keepBytes hP h3).trans h.mu, (h.lay.keepBytes hP h4).trans h.rnd,
    h.fr.trans (frame_ws h.lay h.top.wr h.top.rsp h5 hP.frame)⟩

/-! ## Polynomials in slots -/

/-- Slot `j` holds `f`. -/
abbrev Pl (s : State) (j : Nat) (f : Poly) : Prop := PolyIs s.mem (pa s (pS j)) f

/-- The `m` slots from `b` hold `f 0, …, f (m - 1)`. -/
def Fam (s : State) (b m : Nat) (f : Nat → Poly) : Prop := ∀ j < m, Pl s (b + j) (f j)

/-- The `m` slots from `b` lie apart from `ws`. -/
def famChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (b m : Nat) : Bool := m == 0 || keepB bs ws (pS b) (1024 * m)

theorem famChk_one {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {b m j : Nat} (h : famChk bs ws b m = true) (hj : j < m) :
    keepB bs ws (pS (b + j)) 1024 = true := by
  simp only [famChk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact absurd hj (Nat.not_lt_zero _)
  · refine keepB_sub h ?_ ?_ <;> simp only [oP] <;> omega

theorem Fam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {b m : Nat} {f : Nat → Poly}
    (hc : famChk (rbs ++ wbs) ws b m = true) (h : Fam s b m f) : Fam s' b m f :=
  fun j hj => L.keepPoly hP (famChk_one hc hj) (h j hj)

end VG.Proof.MlDsa.X86_64.Sign
