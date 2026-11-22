module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Top
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-!
# ML-DSA signing on x86-64: a variant's entry to the shared body

`signVia ns n c` stores the addresses of the callees `ns` in the words of a
frame (`fillSlots`), then calls the body `c` that the variants share, which
calls them by those words. What the stores leave (`fillSlots_ok`): the
memory `fillMem`, in which each word holds its callee's address
(`fillMem_read`), changed only in the words (`fillMem_frame`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.MlKem.X86_64 (at_)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The memory after the stores of `vs` to the words from `a + o`. -/
def fillMem (m : Mem) (a : Addr) : Nat → List Addr → Mem
  | _, [] => m
  | o, v :: vs => fillMem (m.writeW (a + BitVec.ofNat 64 o) v) a (o + 8) vs

/-- The word at `a + x`, apart from the words from `a + o`, is as it was. -/
theorem fillMem_other (a : Addr) : ∀ (vs : List Addr) (m : Mem) (o x : Nat),
    (x + 8 ≤ o ∨ o + 8 * vs.length ≤ x) → x < 2 ^ 32 → o + 8 * vs.length < 2 ^ 32 →
    (fillMem m a o vs).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64
  | [], _, _, _, _, _, _ => rfl
  | v :: vs, m, o, x, hx, hx', ho => by
    simp only [List.length_cons] at hx ho
    rw [fillMem, fillMem_other a vs _ (o + 8) x (by omega_using [hx]) hx' (by omega_using [ho]),
      readW_writeW_slot m a v (by omega_using [hx]) hx' (by omega_using [ho])]

/-- The word `i` holds the `i`-th address. -/
theorem fillMem_read (a : Addr) : ∀ (vs : List Addr) (m : Mem) (o i : Nat) (hi : i < vs.length),
    o + 8 * vs.length < 2 ^ 32 →
    (fillMem m a o vs).readW (a + BitVec.ofNat 64 (o + 8 * i)) 64 = vs[i]
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | v :: vs, m, o, 0, _, ho => by
    simp only [List.length_cons] at ho
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [fillMem, fillMem_other a vs _ (o + 8) o (.inl (Nat.le_refl _))
      (by omega_using [ho]) (by omega_using [ho]), Mem.readW_writeW_self64]
    rfl
  | v :: vs, m, o, i + 1, hi, ho => by
    simp only [List.length_cons] at hi ho
    rw [fillMem, show o + 8 * (i + 1) = (o + 8) + 8 * i by omega_using [],
      fillMem_read a vs _ (o + 8) i (by omega_using [hi]) (by omega_using [ho])]
    rfl

/-- The stores change memory only in the words. -/
theorem fillMem_frame (a : Addr) : ∀ (vs : List Addr) (m : Mem) (o : Nat), o + 8 * vs.length < 2 ^ 32 →
    Frame [⟨a + BitVec.ofNat 64 o, 8 * vs.length⟩] m (fillMem m a o vs)
  | [], _, _, _ => Frame.refl _ _
  | v :: vs, m, o, ho => by
    simp only [List.length_cons] at ho
    rw [fillMem]
    have hc : (⟨a + BitVec.ofNat 64 o, 8 * (vs.length + 1)⟩ : Region).Contains (a + BitVec.ofNat 64 o) 8 := by
      have := contains_offset' (base := a + BitVec.ofNat 64 o) (off := 0) (len := 8) (n := 8 * (vs.length + 1))
        (by omega_using []) (by omega_using [ho])
      rwa [BitVec.add_zero] at this
    have h₁ := (Frame.refl [⟨a + BitVec.ofNat 64 o, 8 * (vs.length + 1)⟩] m).writeW (List.mem_singleton_self _) v hc
    have h₂ := fillMem_frame a vs (m.writeW (a + BitVec.ofNat 64 o) v) (o + 8) (by omega_using [ho])
    refine h₁.trans (Frame.sub h₂ fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton] at hr; subst hr
    intro y hy
    simp only [Region.Contains] at hy ⊢
    rw [show a + BitVec.ofNat 64 (o + 8) = (a + BitVec.ofNat 64 o) + BitVec.ofNat 64 8 by
      rw [BitVec.add_assoc, BitVec.ofNat_add]] at hy
    bv_omega_using [hy, ho]

/-- The addresses of `ns` in the words from `rsp + o`, with `rax` as scratch. -/
theorem fillSlots_ok : ∀ (ns : List String) (o : Nat) (s : State),
    (∀ i < ns.length, InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (o + 8 * i)) 8) →
    WP isa (.block (fillSlots o ns)) s fun s' =>
      (s'.mem = fillMem s.mem (s.gpr .rsp) o (ns.map s.syms) ∧ s'.mxcsr = s.mxcsr) ∧ Keep [.rax] s s'
  | [], _, s, _ => WP.block_nil ⟨⟨rfl, rfl⟩, Keep.refl _ _⟩
  | n :: ns, o, s, hw => by
    rw [fillSlots, show (Instr.leaSym .rax n :: .store (at_ .rsp o) .rax :: fillSlots (o + 8) ns) =
      [.leaSym .rax n, .store (at_ .rsp o) .rax] ++ fillSlots (o + 8) ns from rfl, WP.block_append_iff]
    have h0 := hw 0 (by simp)
    rw [Nat.mul_zero, Nat.add_zero] at h0
    refine WP.mono_syms (WP.keep [.rax] (Q := fun s1 =>
      s1.mem = s.mem.writeW (s.gpr .rsp + BitVec.ofNat 64 o) (s.syms n) ∧ s1.mxcsr = s.mxcsr)
      (by xrun [h0]; rfl) (by rfl)) fun s1 ⟨⟨hm, hx⟩, k⟩ hy => ?_
    have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
    refine WP.mono (fillSlots_ok ns (o + 8) s1 fun i hi => ?_) fun s2 ⟨⟨hm2, hx2⟩, k2⟩ =>
      ⟨⟨?_, hx2.trans hx⟩, k.trans k2 |>.mono fun r hr => by simpa using hr⟩
    · rw [hsp, k.2.2, show o + 8 + 8 * i = o + 8 * (i + 1) by omega_using []]
      exact hw (i + 1) (by simp only [List.length_cons]; omega_using [hi])
    · rw [hm2, hm, hsp, hy, List.map_cons, fillMem]

/-- A prepared key is in the bytes of its region. -/
theorem prepared_congr {p : Params} {m m' : Mem} {a : Addr}
    (hb : bytesAt m' a (preparedSecretKeyBytes p) = bytesAt m a (preparedSecretKeyBytes p))
    (h : PreparedSecretKey p m a) : PreparedSecretKey p m' a := by
  have hl : p.skLen + 1024 * (p.ℓ + 2 * p.k) = preparedSecretKeyBytes p := by
    simp only [preparedSecretKeyBytes, n]
  have hsk : bytesAt m' a p.skLen = bytesAt m a p.skLen := by
    rw [← Proof.MlKem.bytesAt_take m' a (show p.skLen ≤ preparedSecretKeyBytes p by omega_using [hl]), hb,
      Proof.MlKem.bytesAt_take m a (show p.skLen ≤ preparedSecretKeyBytes p by omega_using [hl])]
  intro i hi
  rw [hsk]
  have e4 : 4 * n * i = 1024 * i := by simp only [n]
  have hk : p.skLen + 4 * n * i + 1024 ≤ preparedSecretKeyBytes p := by rw [e4]; omega_using [hl, hi]
  refine VG.Proof.MlDsa.polyStored_iff.mpr (VG.Proof.MlDsa.PreparedKey.polyIs_of_copy ?_
    (VG.Proof.MlDsa.polyStored_iff.mp (h i hi)))
  rw [← Proof.MlKem.bytesAt_slice _ _ hk, hb, Proof.MlKem.bytesAt_slice _ _ hk]

theorem toNat_sub_ofNat {sp : Addr} {x : Nat} (h : x ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 x).toNat = sp.toNat - x := by
  have := sp.isLt
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h])]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h])]

/-- `l` bytes `x` bytes below `sp`, within the `n` below it. -/
theorem sub_below {sp : Addr} {x l n : Nat} (hl : l ≤ x) (hn : x ≤ n) (hsp : n ≤ sp.toNat) :
    Region.Sub ⟨sp - BitVec.ofNat 64 x, l⟩ (below sp n) := by
  intro y hy
  simp only [Region.Contains] at hy ⊢
  have h1 := toNat_sub_ofNat (sp := sp) (x := x) (by omega_using [hn, hsp])
  have h2 := toNat_sub_ofNat (sp := sp) (x := n) hsp
  bv_omega_using [hy, h1, h2, hl, hn, hsp]

theorem contains_below {sp : Addr} {x l n : Nat} (hl : l ≤ x) (hn : x ≤ n) (hsp : n ≤ sp.toNat) :
    (below sp n).Contains (sp - BitVec.ofNat 64 x) l := by
  simp only [Region.Contains]
  have h1 := toNat_sub_ofNat (sp := sp) (x := x) (by omega_using [hn, hsp])
  have h2 := toNat_sub_ofNat (sp := sp) (x := n) hsp
  bv_omega_using [h1, h2, hl, hn, hsp]

theorem sub_sub_ofNat (a : Addr) (x y : Nat) :
    a - BitVec.ofNat 64 x - BitVec.ofNat 64 y = a - BitVec.ofNat 64 (x + y) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem sub_add_ofNat (a : Addr) (x y : Nat) (h : y ≤ x) :
    a - BitVec.ofNat 64 x + BitVec.ofNat 64 y = a - BitVec.ofNat 64 (x - y) := by
  rw [show x = (x - y) + y by omega_using [h], ← sub_sub_ofNat, BitVec.sub_add_cancel, Nat.add_sub_cancel]

/-- A word above the one written at `a` is as it was. -/
theorem readW_writeW_base (m : Mem) (a : Addr) (v : BitVec 64) {x : Nat} (hx : 8 ≤ x) (hx' : x < 2 ^ 32) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  have := readW_writeW_slot m a v (x := x) (y := 0) (.inr (by omega_using [hx])) hx' (by decide)
  rwa [BitVec.add_zero] at this

section
variable {p : Params} {D : Nat} {ns : List String} {σ : State}

/-- The regions the body reads: `sk`, `μ`, `rnd` and the callees' words. -/
abbrev viaRd (p : Params) (ns : List String) (σ : State) : List Region :=
  [⟨σ.gpr .rdi, skL p σ⟩, ⟨σ.gpr .rsi, 64⟩, ⟨σ.gpr .rdx, 32⟩,
    ⟨σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns), 8 * ns.length⟩]

/-- The body is entered with memory that differs from `σ`'s only below `rsp`. -/
theorem via_frame (hB : viaBytes ns < 4096) (hsp : D + viaBytes ns + 8 ≤ (σ.gpr .rsp).toNat) {s1 : State}
    (hm1 : s1.mem = fillMem σ.mem (σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns)) 0 (ns.map σ.syms))
    (k1 : Keep [.rax] (allocState (viaBytes ns) σ) s1) (rd wr : List Region) :
    Frame [below (σ.gpr .rsp) (D + viaBytes ns + 8)] σ.mem (s1.callEntry.withRegions rd wr).mem := by
  have hlen : 8 * ns.length + 8 = viaBytes ns := rfl
  have hs1 : s1.gpr .rsp = σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns) := by rw [k1.gpr (by decide), allocState_rsp']
  have hslot : Region.Sub ⟨σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns), 8 * ns.length⟩
      (below (σ.gpr .rsp) (D + viaBytes ns + 8)) :=
    sub_below (by omega_using [hlen]) (by omega_using []) hsp
  have f1 := fillMem_frame (σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns)) (ns.map σ.syms) σ.mem 0
    (by simp only [List.length_map]; omega_using [hB, hlen])
  rw [BitVec.add_zero, List.length_map] at f1
  have f2 : Frame [below (σ.gpr .rsp) (D + viaBytes ns + 8)] σ.mem s1.mem := by
    rw [hm1]; exact Frame.sub f1 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hslot⟩
  have hc : (below (σ.gpr .rsp) (D + viaBytes ns + 8)).Contains (s1.gpr .rsp - 8) 8 := by
    rw [hs1, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub_ofNat]
    exact contains_below (by omega_using []) (by omega_using []) hsp
  rw [State.withRegions_mem, State.callEntry_mem]
  exact f2.writeW (List.mem_singleton_self _) _ hc

/-- The state after the stores is entered in the body's contract. -/
theorem via_pre (hns : ns ≠ []) (hB : viaBytes ns < 4096) (hp : (signK p (D + viaBytes ns + 8)).pre σ) {s1 : State}
    (hm1 : s1.mem = fillMem σ.mem (σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns)) 0 (ns.map σ.syms))
    (k1 : Keep [.rax] (allocState (viaBytes ns) σ) s1) (hy1 : s1.syms = σ.syms) :
    (signKS p D ns).pre (s1.callEntry.withRegions (viaRd p ns σ) σ.wr) := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1', k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp,
    hprep⟩ := hp'
  generalize hB' : viaBytes ns = B at *
  have hlen : 8 * ns.length + 8 = B := hB'
  obtain ⟨t, ht⟩ : ∃ t, t = s1.callEntry.withRegions (viaRd p ns σ) σ.wr := ⟨_, rfl⟩
  have hrd' : t.rd = viaRd p ns σ := by rw [ht]; rfl
  have hwr' : t.wr = σ.wr := by rw [ht]; rfl
  have hmt : t.mem = s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0) := by rw [ht]; rfl
  have hsy : t.syms = σ.syms := by rw [ht]; exact hy1
  rw [← ht]
  have eg : ∀ r, r ≠ .rsp → r ≠ .rax → t.gpr r = σ.gpr r := fun r h1 h2 => by
    rw [ht, State.withRegions_gpr, State.callEntry_gpr _ h1, k1.gpr (by simpa using h2), allocState_gpr' _ _ h1]
  have hs1 : s1.gpr .rsp = σ.gpr .rsp - BitVec.ofNat 64 B := by rw [k1.gpr (by decide), allocState_rsp']
  have esp : t.gpr .rsp = σ.gpr .rsp - BitVec.ofNat 64 (B + 8) := by
    rw [ht, State.withRegions_gpr, State.callEntry_rsp, hs1]; exact sub_sub_ofNat _ _ 8
  have e1 := eg .rdi (by decide) (by decide)
  have e2 := eg .rsi (by decide) (by decide)
  have e3 := eg .rdx (by decide) (by decide)
  have e4 := eg .rcx (by decide) (by decide)
  have e5 := eg .r8 (by decide) (by decide)
  have e9 := eg .r9 (by decide) (by decide)
  have hL : skL p t = skL p σ := by simp only [skL, e9]
  have hret : Region.Sub ⟨σ.gpr .rsp - BitVec.ofNat 64 (B + 8), 8⟩ (below (σ.gpr .rsp) (D + B + 8)) :=
    sub_below (by omega_using []) (by omega_using []) hsp
  have hbel : Region.Sub (below (σ.gpr .rsp - BitVec.ofNat 64 (B + 8)) D) (below (σ.gpr .rsp) (D + B + 8)) := by
    have := below_below (σ.gpr .rsp) (B + 8) D
    rwa [show D + (B + 8) = D + B + 8 by omega_using []] at this
  have hslot : Region.Sub ⟨σ.gpr .rsp - BitVec.ofNat 64 B, 8 * ns.length⟩ (below (σ.gpr .rsp) (D + B + 8)) :=
    sub_below (by omega_using [hlen]) (by omega_using []) hsp
  have hsR : slotR ns t = ⟨σ.gpr .rsp - BitVec.ofNat 64 B, 8 * ns.length⟩ := by
    simp only [slotR, esp]
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_add_ofNat (σ.gpr .rsp) (B + 8) 8 (by omega_using []),
      Nat.add_sub_cancel]
  have hspN : (t.gpr .rsp).toNat = (σ.gpr .rsp).toNat - (B + 8) := by
    rw [esp]; exact toNat_sub_ofNat (by omega_using [hsp])
  -- the memory the body is entered with differs from `σ`'s only below `rsp`
  have hfr : Frame [below (σ.gpr .rsp) (D + B + 8)] σ.mem t.mem := by
    have f1 := fillMem_frame (σ.gpr .rsp - BitVec.ofNat 64 B) (ns.map σ.syms) σ.mem 0
      (by simp only [List.length_map]; omega_using [hB, hlen])
    rw [BitVec.add_zero, List.length_map] at f1
    have f2 : Frame [below (σ.gpr .rsp) (D + B + 8)] σ.mem s1.mem := by
      rw [hm1]; exact Frame.sub f1 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hslot⟩
    have hc : (below (σ.gpr .rsp) (D + B + 8)).Contains (s1.gpr .rsp - 8) 8 := by
      rw [hs1, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub_ofNat]
      exact contains_below (by omega_using []) (by omega_using []) hsp
    rw [hmt]
    exact f2.writeW (List.mem_singleton_self _) _ hc
  have hby : ∀ {a : Addr} {l : Nat}, (below (σ.gpr .rsp) (D + B + 8)).Disjoint ⟨a, l⟩ → l ≤ 2 ^ 64 →
      bytesAt t.mem a l = bytesAt σ.mem a l := fun hd hl =>
    VG.Proof.MlKem.bytesAt_frame hfr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd.symm) hl
  refine ⟨?_, ?_, .inr ?_, fun i hi => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [hrd', hwr', hL, e1, e2, e3, e4, e5, e9, hspN]
    · simp only [slotRs, hns, ↓reduceIte, hsR, viaRd, List.cons_append, List.nil_append, hB']
    · exact hwr
    · exact d1
    · exact d2
    · exact d3
    · exact d4
    · exact d5
    · exact d6
    · exact d7
    · simp only [retR, esp]; exact k1'.sub_left hret
    · simp only [retR, esp]; exact k2.sub_left hret
    · simp only [retR, esp]; exact k3.sub_left hret
    · simp only [retR, esp]; exact k4.sub_left hret
    · simp only [retR, esp]; exact k5.sub_left hret
    · rw [esp]; exact k1'.sub_left hbel
    · rw [esp]; exact k2.sub_left hbel
    · rw [esp]; exact k3.sub_left hbel
    · rw [esp]; exact k4.sub_left hbel
    · rw [esp]; exact k5.sub_left hbel
    · exact n1
    · exact n2
    · exact n3
    · exact n4
    · exact n5
    · omega_using [hsp]
    · intro h9
      have hk := hprep h9
      have hsk : skL p σ = preparedSecretKeyBytes p := by simp only [skL, h9, ite_false]
      rw [hsk] at k1' n1
      exact prepared_congr (hby k1' (by omega_using [n1])) hk
  · intro r hr
    rw [hsR]
    rw [hwr', hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [k4.sub_left hslot, k5.sub_left hslot]
  · rw [hspN]; have := (σ.gpr .rsp).isLt; omega_using [hsp, hlen]
  · -- the callee's word `i`
    have ha : t.gpr .rsp + BitVec.ofNat 64 (8 + 8 * i) =
        (σ.gpr .rsp - BitVec.ofNat 64 B - 8) + BitVec.ofNat 64 (8 + 8 * i) := by
      rw [esp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub_ofNat]
    have hb : (σ.gpr .rsp - BitVec.ofNat 64 B - 8) + BitVec.ofNat 64 (8 + 8 * i) =
        (σ.gpr .rsp - BitVec.ofNat 64 B) + BitVec.ofNat 64 (0 + 8 * i) := by
      rw [BitVec.ofNat_add 8, BitVec.ofNat_add 0]; bv_omega
    have hin : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 (8 + 8 * i)) 8 := by
      refine ⟨⟨σ.gpr .rsp - BitVec.ofNat 64 B, 8 * ns.length⟩, List.mem_append_left _ (by rw [hrd']; simp [viaRd, hB']), ?_⟩
      rw [ha, hb]
      exact contains_offset' (by omega_using [hi]) (by omega_using [hB, hlen])
    simp only [State.load64, hin, ↓reduceIte]
    congr 1
    rw [hmt, hs1, ha, readW_writeW_base _ _ _ (by omega_using []) (by omega_using [hi, hB, hlen]), hb, hm1,
      fillMem_read _ _ _ 0 i (by simpa using hi) (by simp only [List.length_map]; omega_using [hB, hlen]),
      hsy, List.getElem_map]

end

/-- The return address is apart from bytes below `rsp`. -/
theorem ret_disj {sp : Addr} {x l : Nat} (hl : l ≤ x) (hx : x < 2 ^ 63) :
    Region.Disjoint ⟨sp, 8⟩ ⟨sp - BitVec.ofNat 64 x, l⟩ := by
  intro y h1 h2
  simp only [Region.Contains] at h1 h2
  bv_omega_using [h1, h2, hl, hx]

theorem freeState_gpr {bytes : Nat} {t : State} {r : Reg} (h : r ≠ .rsp) : (freeState bytes t).gpr r = t.gpr r := by
  simp [freeState, State.setReg, h]

section
variable {p : Params} {D : Nat} {ns : List String} {σ : State}

/-- `signVia` from a state of `signK` with room for its frame and the call:
the body, run by the words of the frame, does what `signK` says. -/
theorem signVia_ok (hns : ns ≠ []) (hB : viaBytes ns < 4096) {n : String} {c : Prog isa}
    (hv : ∀ s, (signKS p D ns).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (signKS p D ns).post s s')
    (hsp : NoSp c) (hd : 8 * (c.depth + 1) ≤ D) (hD : D < 2 ^ 32)
    (hp : (signK p (D + viaBytes ns + 8)).pre σ) :
    WP isa (signVia ns n c) σ fun s' => abiPreserved σ s' ∧ (signK p (D + viaBytes ns + 8)).post σ s' := by
  have hp' := hp
  obtain ⟨hrd, hwr, _, _, _, _, _, _, _, _, _, _, r4, r5, k1', k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp0, -⟩ := hp'
  have hlen : 8 * ns.length + 8 = viaBytes ns := rfl
  have hw0 : ∀ i < ns.length, InRegions (allocState (viaBytes ns) σ).wr
      ((allocState (viaBytes ns) σ).gpr .rsp + BitVec.ofNat 64 (0 + 8 * i)) 8 := fun i hi =>
    ⟨⟨σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns), viaBytes ns⟩, List.mem_cons_self .., by
      rw [allocState_rsp']; exact contains_offset' (by omega_using [hi, hlen]) (by omega_using [hB])⟩
  unfold signVia
  refine alloc_frame_ok ⟨by omega_using [hlen], hB, by omega_using [hlen]⟩ (by omega_using [hsp0]) ?_
  refine WP.seq (WP.mono_syms (fillSlots_ok ns 0 _ hw0) fun s1 ⟨⟨hm1, hx1⟩, k1⟩ hy1 => ?_)
  have hm1' : s1.mem = fillMem σ.mem (σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns)) 0 (ns.map σ.syms) := by
    rw [hm1, allocState_rsp']; rfl
  have hs1 : s1.gpr .rsp = σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns) := by rw [k1.gpr (by decide), allocState_rsp']
  have hrd1 : s1.rd = σ.rd := k1.2.1
  have hwr1 : s1.wr = ⟨σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns), viaBytes ns⟩ :: σ.wr := k1.2.2
  have hc : Covers (viaRd p ns σ ++ σ.wr) (s1.rd ++ s1.wr) := by
    rw [hrd1, hwr1, hrd]
    refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ (Covers.cons ?_ (Covers.cons ?_ Covers.nil))))
      (Covers.of_mem fun r hr => List.mem_append_right _ (List.mem_cons_of_mem _ hr))
    · exact Covers.of_mem fun r hr => by simp at hr; subst hr; simp
    · exact Covers.of_mem fun r hr => by simp at hr; subst hr; simp
    · exact Covers.of_mem fun r hr => by simp at hr; subst hr; simp
    · have hc0 : (⟨σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns), viaBytes ns⟩ : Region).Contains
          (σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns)) (8 * ns.length) := by
        have := contains_offset' (base := σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns)) (off := 0)
          (len := 8 * ns.length) (n := viaBytes ns) (by omega_using [hlen]) (by omega_using [hB])
        rwa [BitVec.add_zero] at this
      exact Covers.one ⟨_, by simp, hc0⟩
  have hw : Covers σ.wr s1.wr := Covers.of_mem fun r hr => by rw [hwr1]; exact List.mem_cons_of_mem _ hr
  refine WP.call_mx hv hsp (by omega_using [hd, hD]) (via_pre hns hB hp hm1' k1 hy1) hc hw
    fun s' hrd' hwr' hcs hf _ hpost hmx => ⟨by rw [hcs .rsp (by decide), k1.gpr (by decide)], hwr'.trans k1.2.2,
      fun m u hm => ?_⟩
  have hsp' : s'.gpr .rsp = (allocState (viaBytes ns) σ).gpr .rsp := by rw [hcs .rsp (by decide), k1.gpr (by decide)]
  have eg : ∀ r, r ≠ .rsp → r ≠ .rax → s1.gpr r = σ.gpr r := fun r h1 h2 => by
    rw [k1.gpr (by simpa using h2), allocState_gpr' _ _ h1]
  have fg : ∀ r, r ≠ .rsp → (freeState (viaBytes ns) s').gpr r = s'.gpr r := fun r h => freeState_gpr h
  have fsp : (freeState (viaBytes ns) s').gpr .rsp = σ.gpr .rsp := freeState_rsp hsp'
  have hsub : 8 * (c.depth + 1) ≤ D := hd
  -- the return address
  have hr1 : s1.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64 := by
    have f1 := fillMem_frame (σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns)) (ns.map σ.syms) σ.mem 0
      (by simp only [List.length_map]; omega_using [hB, hlen])
    rw [BitVec.add_zero, List.length_map, ← hm1'] at f1
    refine f1.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton] at hr; subst hr
    exact ret_disj (by omega_using [hlen]) (by omega_using [hB])
  have hr2 : s'.mem.readW (σ.gpr .rsp) 64 = s1.mem.readW (σ.gpr .rsp) 64 := by
    refine hf.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · rw [hwr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [r4, r5]
    · rw [List.mem_singleton] at hr; subst hr
      rw [hs1]
      show Region.Disjoint _ ⟨σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns) - BitVec.ofNat 64 (8 * (c.depth + 1)),
        8 * (c.depth + 1)⟩
      rw [sub_sub_ofNat]
      exact ret_disj (by omega_using []) (by omega_using [hB, hD, hsub])
  have hr3 : m.readW (σ.gpr .rsp) 64 = s'.mem.readW (σ.gpr .rsp) 64 := by
    refine hm.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton] at hr; subst hr
    exact ret_disj (Nat.le_refl _) (by omega_using [hB])
  have hfrm : Region.Sub ⟨σ.gpr .rsp - BitVec.ofNat 64 (viaBytes ns), viaBytes ns⟩
      (below (σ.gpr .rsp) (D + viaBytes ns + 8)) := sub_below (Nat.le_refl _) (by omega_using []) hsp0
  refine ⟨⟨fun r hr => ?_, hr3.trans (hr2.trans hr1), ?_⟩, ?_⟩
  · by_cases h : r = .rsp
    · subst h; exact fsp
    · have hax : r ≠ .rax := fun e => by subst e; exact absurd hr (by decide)
      show (freeState (viaBytes ns) s').gpr r = σ.gpr r
      rw [fg r h, hcs r hr, eg r h hax]
  · show s'.mxcsr.extractLsb' 6 10 = σ.mxcsr.extractLsb' 6 10
    rw [hmx, hx1]; rfl
  · obtain ⟨s₂, hm₂, hg₂, hq⟩ := hpost
    have hfr := via_frame (D := D) hB hsp0 hm1' k1 (viaRd p ns σ) σ.wr
    have hby : ∀ {a : Addr} {l : Nat}, (below (σ.gpr .rsp) (D + viaBytes ns + 8)).Disjoint ⟨a, l⟩ → l ≤ 2 ^ 64 →
        bytesAt (s1.callEntry.withRegions (viaRd p ns σ) σ.wr).mem a l = bytesAt σ.mem a l := fun hd hl =>
      VG.Proof.MlKem.bytesAt_frame hfr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd.symm) hl
    have tg : ∀ r, r ≠ .rsp → r ≠ .rax → (s1.callEntry.withRegions (viaRd p ns σ) σ.wr).gpr r = σ.gpr r :=
      fun r h1 h2 => by rw [State.withRegions_gpr, State.callEntry_gpr _ h1, eg r h1 h2]
    have hsk := skLen_le_skL p σ
    show Outcome _ _ _
    have h' : Outcome _ _ _ := hq
    rw [tg .rdi (by decide) (by decide), tg .rsi (by decide) (by decide), tg .rdx (by decide) (by decide),
      tg .rcx (by decide) (by decide), hby (k1'.sub_right (Region.sub_prefix hsk)) (by omega_using [n1, hsk]),
      hby k2 (by omega_using []), hby k3 (by omega_using []), hm₂, hg₂ .rax (by decide)] at h'
    have hsig : bytesAt m (σ.gpr .rcx) p.sigLen = bytesAt s'.mem (σ.gpr .rcx) p.sigLen :=
      VG.Proof.MlKem.bytesAt_frame hm (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact (k4.sub_left hfrm).symm) (by omega_using [n4])
    show Outcome _ (((freeState (viaBytes ns) s').gpr .rax).setWidth 32) (bytesAt m (σ.gpr .rcx) p.sigLen)
    rw [fg .rax (by decide), hsig]
    exact h'

end

end VG.Proof.MlDsa.X86_64.Sign
