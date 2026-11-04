module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Search
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SearchInit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The search's entry: its frame's words from the arguments and the state -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Search
open VG.Spec.RsaKeyGen (primeEntropy)

def headValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r12), (5, s.gpr .rdi), (6, s.gpr .rsi), (7, s.gpr .rdx), (8, s.gpr .rcx),
    (9, s.gpr .r8), (10, s.gpr .r9)]

def argValues (s : State) : List (Nat × BitVec 64) :=
  [(11, stackArg s 0), (12, stackArg s 1), (13, stackArg s 2), (14, stackArg s 3),
    (15, stackArg s 4), (18, stackArg s 5)]

def wordValues (s : State) : List (Nat × BitVec 64) :=
  [(0, s.mem.readW (stackArg s 5) 64), (1, s.gpr .rsi),
    (2, (s.gpr .rsi <<< 15) + s.gpr .rsi), (3, 0), (16, 0)]

def entryValues (s : State) : List (Nat × BitVec 64) := headValues s ++ argValues s ++ wordValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, headValues, argValues, wordValues, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl) <;> dsimp only <;> decide

theorem arg_contains (s : State) {j : Nat} (hj : j < 6) :
    (inArgs s).Contains (stackArgAddr s j) 8 := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega]
  exact Offset.contains_base _ (by omega) (by omega)

theorem input_args {p : SearchPublic} {s : State} (h : SearchInput p s) :
    ∀ j < 6, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := by
  intro j hj
  refine ⟨inArgs s, ?_, arg_contains s hj⟩
  rw [h.1.2.2.1]
  exact List.mem_append_left _ (by simp [inReads])

/-- The caller's stack argument `k`, from inside the frame. -/
theorem callerArg_addr (sp : Addr) (k : Nat) :
    sp - BitVec.ofNat 64 160 + BitVec.ofNat 64 (160 + 8 + 8 * k) = sp + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [show 160 + 8 + 8 * k = 160 + 8 * (k + 1) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- The frame's stores keep what is outside it. -/
theorem entry_frame {p : SearchPublic} {s : State} (h : SearchInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {r : Region} (hr : r ∈ inWrites s ++ inReads s) {a : Addr} {n : Nat}
    (ha : r.Contains a (n / 8)) (hn : n / 8 < 2 ^ 64) :
    (writeFrame s.mem p.F values).readW a n = s.mem.readW a n := by
  refine (writeFrame_frame s.mem p.F values hb).readW ha (fun q hq => ?_) hn
  obtain rfl := List.mem_singleton.mp hq
  exact fun x hx hy => (h.stack_disjoint hr).2 x (h.frame_sub x hy) hx

theorem alloc_rsp {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 160 s).gpr .rsp = p.F := by
  rw [allocated_rsp, ← h.sp_eq]

theorem alloc_wr {p : SearchPublic} {s : State} (h : SearchInput p s) :
    (allocated 160 s).wr = p.frame :: s.wr := by
  show (⟨s.gpr .rsp - BitVec.ofNat 64 160, 160⟩ : Region) :: s.wr = _
  rw [← h.sp_eq]

theorem entry_head_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entryHead) (allocated 160 s) fun t =>
      t.gpr .r12 = p.F ∧ t.mem = writeFrame s.mem p.F (headValues s) ∧
      Keep [.r12] (allocated 160 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 160 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hsp := alloc_rsp h
  refine WP.mono (WP.keep [.r12] (Q := fun t =>
    t.gpr .r12 = p.F ∧ t.mem = writeFrame s.mem p.F (headValues s)) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold entryHead writeFrame headValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hsp,
    allocated_reg _ _ _ (show Reg.r12 ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    allocated_reg _ _ _ (show Reg.rsi ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.rdx ≠ .rsp by decide),
    allocated_reg _ _ _ (show Reg.rcx ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.r8 ≠ .rsp by decide),
    allocated_reg _ _ _ (show Reg.r9 ≠ .rsp by decide), allocated_mem,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 56 (by decide), hs 64 (by decide),
    hs 72 (by decide), hs 80 (by decide)]

theorem arg_addr {p : SearchPublic} {s : State} (h : SearchInput p s) (k : Nat) :
    p.F + BitVec.ofNat 64 (168 + 8 * k) = stackArgAddr s k := by
  rw [show 168 + 8 * k = 160 + 8 + 8 * k by omega, callerArg_addr, h.sp_eq]
  rfl

/-- The caller's stack arguments, after stores to the frame. -/
theorem arg_read {p : SearchPublic} {s : State} (h : SearchInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {k : Nat} (hk : k < 6) :
    (writeFrame s.mem p.F values).readW (p.F + BitVec.ofNat 64 (168 + 8 * k)) 64 = stackArg s k := by
  rw [arg_addr h]
  exact entry_frame h values hb (r := inArgs s) (by simp [inReads]) (arg_contains s hk) (by decide)

theorem arg_in {p : SearchPublic} {s : State} (h : SearchInput p s) {t : State} (hr : t.rd = s.rd)
    (hw : t.wr = p.frame :: s.wr) {k : Nat} (hk : k < 6) :
    InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 (168 + 8 * k)) 8 := by
  rw [arg_addr h, hr, hw]
  obtain ⟨r, hr', hc⟩ := input_args h k hk
  refine ⟨r, ?_, hc⟩
  rcases List.mem_append.mp hr' with hm | hm
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)

theorem entry_args_ok {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hm : t.mem = writeFrame s.mem p.F (headValues s)) (k : Keep [.r12] (allocated 160 s) t)
    (hr : t.gpr .r12 = p.F) :
    WP isa (.block entryArgs) t fun u =>
      u.gpr .rax = stackArg s 5 ∧ u.mem = writeFrame t.mem p.F (argValues s) ∧ Keep [.rax] t u := by
  have hb : ∀ e ∈ headValues s, e.1 < 20 := fun e he =>
    entryValues_bound s e (List.mem_append_left _ (List.mem_append_left _ he))
  have htr : t.rd = s.rd := k.2.1
  have htw : t.wr = p.frame :: s.wr := k.2.2.trans (alloc_wr h)
  have hsp : t.gpr .rsp = p.F := (k.gpr (by decide)).trans (alloc_rsp h)
  have scr := h.frame_scr htw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions t.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hv0 : t.mem.readW (p.F + BitVec.ofNat 64 168) 64 = stackArg s 0 := by
    rw [hm]; exact arg_read h _ hb (k := 0) (by decide)
  have hv1 : t.mem.readW (p.F + BitVec.ofNat 64 176) 64 = stackArg s 1 := by
    rw [hm]; exact arg_read h _ hb (k := 1) (by decide)
  have hv2 : t.mem.readW (p.F + BitVec.ofNat 64 184) 64 = stackArg s 2 := by
    rw [hm]; exact arg_read h _ hb (k := 2) (by decide)
  have hv3 : t.mem.readW (p.F + BitVec.ofNat 64 192) 64 = stackArg s 3 := by
    rw [hm]; exact arg_read h _ hb (k := 3) (by decide)
  have hv4 : t.mem.readW (p.F + BitVec.ofNat 64 200) 64 = stackArg s 4 := by
    rw [hm]; exact arg_read h _ hb (k := 4) (by decide)
  have hv5 : t.mem.readW (p.F + BitVec.ofNat 64 208) 64 = stackArg s 5 := by
    rw [hm]; exact arg_read h _ hb (k := 5) (by decide)
  have ha0 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 168) 8 := arg_in h htr htw (k := 0) (by decide)
  have ha1 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 176) 8 := arg_in h htr htw (k := 1) (by decide)
  have ha2 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 184) 8 := arg_in h htr htw (k := 2) (by decide)
  have ha3 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 192) 8 := arg_in h htr htw (k := 3) (by decide)
  have ha4 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 200) 8 := arg_in h htr htw (k := 4) (by decide)
  have ha5 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 208) 8 := arg_in h htr htw (k := 5) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun u =>
    u.gpr .rax = stackArg s 5 ∧ u.mem = writeFrame t.mem p.F (argValues s)) ?_ rfl)
    fun _ ⟨⟨hra, hu⟩, ku⟩ => ⟨hra, hu, ku⟩
  unfold entryArgs writeFrame argValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, callerArg, frameBytes, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast,
    Nat.reduceMul, Nat.reduceAdd, hsp, hr, read_above_store, hv0, hv1, hv2, hv3, hv4, hv5,
    ha0, ha1, ha2, ha3, ha4, ha5,
    hs 88 (by decide), hs 96 (by decide), hs 104 (by decide), hs 112 (by decide), hs 120 (by decide),
    hs 144 (by decide)]

theorem entry_words_ok {p : SearchPublic} {s u : State} (h : SearchInput p s)
    (hm : u.mem = writeFrame s.mem p.F (headValues s ++ argValues s))
    (hra : u.gpr .rax = stackArg s 5) (hsi : u.gpr .rsi = s.gpr .rsi) (hr : u.gpr .r12 = p.F)
    (huw : u.wr = p.frame :: s.wr) :
    WP isa (.block entryWords) u fun t =>
      t.mem = writeFrame u.mem p.F (wordValues s) ∧ Keep [.rax, .rcx] u t := by
  have hb : ∀ e ∈ headValues s ++ argValues s, e.1 < 20 := fun e he =>
    entryValues_bound s e (List.mem_append_left _ he)
  have scr := h.frame_scr huw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions u.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hst : (inState s).Contains (stackArg s 5) 8 := by
    simp only [inState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
    decide
  have hs0 : InRegions u.wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hv : u.mem.readW (stackArg s 5) 64 = s.mem.readW (stackArg s 5) 64 := by
    rw [hm]
    exact entry_frame h _ hb (r := inState s) (by simp [inWrites]) hst (by decide)
  have ha : InRegions (u.rd ++ u.wr) (stackArg s 5) 8 := by
    refine ⟨inState s, ?_, hst⟩
    rw [huw, h.1.2.2.2.1]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold entryWords writeFrame wordValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    hra, hsi, hr, hv, ha, hs0, hs 8 (by decide), hs 16 (by decide), hs 24 (by decide),
    hs 128 (by decide)]
  rfl

theorem entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) (allocated 160 s) fun t =>
      t.gpr .r12 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s) ∧
      Keep [.rax, .rcx, .r12] (allocated 160 s) t := by
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entry_head_ok h) fun t ⟨hr, hm, k⟩ => ?_
  refine WP.mono (entry_args_ok h hm k hr) fun u ⟨hra, hu, ku⟩ => ?_
  have huw : u.wr = p.frame :: s.wr := ku.2.2.trans (k.2.2.trans (alloc_wr h))
  have hsi : u.gpr .rsi = s.gpr .rsi := by
    rw [ku.gpr (by decide), k.gpr (by decide), allocated_reg _ _ _ (by decide)]
  have hur12 : u.gpr .r12 = p.F := (ku.gpr (by decide)).trans hr
  refine WP.mono (entry_words_ok h (by rw [hu, hm, writeFrame_append]) hra hsi hur12 huw)
    fun t ⟨ht, kt⟩ => ⟨(kt.gpr (by decide)).trans hur12, ?_, ((k.trans ku).trans kt).mono (by decide)⟩
  rw [ht, hu, hm, entryValues, writeFrame_append, writeFrame_append]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

/-- The search's state on entering its loop. -/
theorem search_start {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) (allocated 160 s) (SearchLive p s 0 p.remaining) := by
  refine WP.mono (entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hb := entryValues_bound s
  have hw (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hm]; exact writeFrame_word _ _ _ hb j hj
  have hf : Frame (SearchInput.changes s) s.mem t.mem := by
    rw [hm]
    apply (writeFrame_frame s.mem p.F _ hb).sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [SearchInput.changes], h.frame_sub⟩
  have hL : p.len ≤ 512 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.1.2.1
  have hsi : s.gpr .rsi = BitVec.ofNat 64 p.len := by rw [← h.2]; exact (ofNat_toNat64 _).symm
  have hcap : (s.gpr .rsi <<< 15) + s.gpr .rsi = BitVec.ofNat 64 (primeEntropy p.len) := by
    rw [hsi, SearchInit.shl_ofNat _ _ (by omega), SearchInit.add_ofNat]
    unfold primeEntropy; congr 1; omega
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.2.1, k.2.2.trans (alloc_wr h),
    (k.gpr (by decide)).trans (alloc_rsp h), hr, fun r hr hn hs => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.gpr (by revert r; decide), allocated_reg _ _ _ hs]
  · change word t.mem p.F (8 * 4) = _
    rw [hw 4 (by decide)]
    rfl
  · rw [h.random_frame hf]; rw [← h.2]; rfl
  · rw [h.e_frame hf]; rw [← h.2]; rfl
  · rw [h.p_frame hf]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (SearchPublic.headers_bound _ _ _ e he)]
    rw [← h.2] at he hcap hsi ⊢
    simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      simp only [frameValue, entryValues, headValues, argValues, wordValues, List.cons_append,
        List.nil_append, List.foldl_cons, List.foldl_nil, searchOfState, searchRemaining, searchLen,
        ofNat_toNat64, hcap, BitVec.add_zero, Nat.sub_zero, Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.X86_64.Search
