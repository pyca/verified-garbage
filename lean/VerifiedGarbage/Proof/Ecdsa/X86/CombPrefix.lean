import VerifiedGarbage.Proof.Ecdsa.X86.CombMain
import VerifiedGarbage.Proof.Framework.X86.SymFrame

/-! # Public static tables at the x86 P-256 entry points -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass

/-- The static tables are immutable, fit the 32-bit address space, and miss
all writable or reserved regions supplied by the caller. -/
def TblsHeld (c : Cfg) (s : State) (wr : List Region) : Prop :=
  Abi.constsHeld s.mem (fun n => (s.syms n).setWidth 64) c.combConsts ∧
    ∀ t ∈ Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts,
      t.base.toNat + t.len ≤ 2 ^ 32 ∧ ∀ r ∈ wr, t.Disjoint r

variable {c : Cfg}

/-- The balanced symbol frame keeps the signing arguments and permissions. -/
theorem Pre.symAddr {s t : State} {extra : List Region} {name : String}
    (hp : Pre c s extra) (h : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) :
    Pre c t extra := by
  have he := h.gpr .esp (by decide)
  have ha : ∀ j < 5, arg t j = arg s j := fun j hj => h.arg hsp (by have := hp.sp_fit; omega)
  have hargs : argAddr t 0 = argAddr s 0 := by simp only [argAddr, he]
  exact {
    rd := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.rd
    wr := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.wr
    out_sc := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.out_sc
    out_d := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.out_d
    out_digest := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.out_digest
    out_k := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.out_k
    d_sc := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.d_sc
    digest_sc := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.digest_sc
    k_sc := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.k_sc
    args_out := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.args_out
    args_sc := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.args_sc
    ret_out := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.ret_out
    ret_sc := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.ret_sc
    out_fit := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.out_fit
    d_fit := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.d_fit
    digest_fit := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.digest_fit
    k_fit := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.k_fit
    sc_fit := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.sc_fit
    sp_fit := by
      simpa only [outR, dR, digestR, kR, scR, argsR, retR, ptr, h.rd, h.wr, he, hargs,
        ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)] using hp.sp_fit
  }

theorem tbl_of_held {d : CombData} (hcd : c.comb = some d) {s₀ s : State} {base : Addr}
    (ht : TblsHeld c s₀ s₀.wr) (hsc : (⟨base, size⟩ : Region) ∈ s₀.wr)
    (hrd : ∀ r ∈ Abi.constRegions (fun n => (s₀.syms n).setWidth 64) c.combConsts, r ∈ s.rd)
    (hu : Unch base [(0, size)] s₀.mem s.mem) :
    TblMem s ((s₀.syms d.tsym).setWidth 64) (c.combWords d) ∧ ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((s₀.syms d.tsym).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
  have hcc : c.combConsts = [(d.tsym, c.combWords d)] := by simp [Cfg.combConsts, hcd]
  obtain ⟨held, fit⟩ := ht
  rw [hcc] at held fit hrd
  obtain ⟨hf, hdj⟩ := fit _ (List.mem_singleton_self _)
  have hsc' : Region.Disjoint ⟨(s₀.syms d.tsym).setWidth 64, 8 * (c.combWords d).length⟩ ⟨base, size⟩ := hdj _ hsc
  dsimp only at hf
  have hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base ((s₀.syms d.tsym).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) :=
    fun i hi b hb => by
      have hc : (⟨(s₀.syms d.tsym).setWidth 64, 8 * (c.combWords d).length⟩ : Region).Contains
          ((s₀.syms d.tsym).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) 1 := by
        rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
      have := hsc' _ hc
      simp only [Region.Contains] at this
      unfold ofs; omega
  refine ⟨⟨hf, ⟨⟨(s₀.syms d.tsym).setWidth 64, 8 * (c.combWords d).length⟩,
    List.mem_append_left _ (hrd _ (by simp [Abi.constRegions])),
    by simp [Region.Contains]⟩, fun i hi => ?_⟩, hout⟩
  rw [← held _ (List.mem_singleton_self _) i hi]
  refine Mem.readW_congr fun b hb => (hu _ fun w hw => ?_)
  rw [List.mem_singleton.mp hw]
  exact Or.inr (by have := hout i hi b (by omega); dsimp only; omega)


/-- Loading the address does not change the immutable table bytes. -/
theorem TblsHeld.symAddr {s t : State} {name : String}
    (ht : TblsHeld c s (below (s.gpr .esp) 4 :: s.wr)) (h : SymAddrPost name s t) :
    TblsHeld c t t.wr := by
  obtain ⟨held, fit⟩ := ht
  refine ⟨?_, ?_⟩
  · intro tab htab i hi
    rw [h.syms, ← held tab htab i hi]
    have ht : (⟨(s.syms tab.1).setWidth 64, 8 * tab.2.length⟩ : Region) ∈
        Abi.constRegions (fun n => (s.syms n).setWidth 64) c.combConsts :=
      List.mem_map_of_mem htab
    obtain ⟨hf, hd⟩ := fit _ ht
    dsimp only at hf
    exact h.frame.readW (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => hd r (List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))) (by decide)
  · intro tab htab
    rw [h.syms] at htab
    obtain ⟨hf, hd⟩ := fit tab htab
    exact ⟨hf, fun r hr => hd r (List.mem_cons_of_mem _ (h.wr ▸ hr))⟩

/-- The body preserves the return word as well as the callee-saved registers. -/
theorem SignKeep.abi {s t : State} {extra : List Region} (hp : Pre c s extra)
    (h : SignKeep c s t) : abiPreserved s t := by
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.saved (.ebx, 0) (by decide)
    · exact h.saved (.esi, 4) (by decide)
    · exact h.saved (.edi, 8) (by decide)
    · exact h.saved (.ebp, 12) (by decide)
    · exact h.esp
  · obtain ⟨m, hU, hO⟩ := h.frame
    have hU' : Outside (ptr s 4) 0 size s.mem m :=
      hU.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    refine Mem.readW_congr fun i hi => ?_
    have h4 : i < 4 := by omega
    rw [← keep_of_disjoint' hU' hp.ret_sc (by decide) h4 (by decide),
      ← keep_of_disjoint' hO hp.ret_out (by have := hp.out_fit; omega) h4 (by decide)]

/-- The prefix leaves a readable input buffer unchanged when it misses
its four-byte temporary stack slot. -/
theorem prefix_bytesAt {name : String} {s t : State} (h : SymAddrPost name s t)
    {r : Region} (hd : r.Disjoint (below (s.gpr .esp) 4)) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt t.mem r.base r.len = Spec.Ecdsa.bytesAt s.mem r.base r.len := by
  unfold Spec.Ecdsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact h.frame.bytes (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact hd) hn (List.mem_range.mp hi)


end VG.Proof.Ecdsa.X86
