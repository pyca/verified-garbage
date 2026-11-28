module

-- separate module: the leaves, which the later stages of the proof (`ForsTree`, `ForsSub`) do not rebuild when they change

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
public import VerifiedGarbage.Proof.SlhDsa.ForsSpec
public import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Fors
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign`, its calls of `thash4`, four leaves

A call of `thash4` on the lanes `A` or `B` of `scratch` (`t4g_ok`): each
lane's output is SHAKE256 of its message; only the outputs, `work` (but its
table) and the stack change.

`leafBody`: four leaves `j` to `j + 3` of a subtree, their private key
values (`PRF` of the addresses of type `FORS_PRF`), the one of the tree's
index XORed into the signature under a mask, and the leaves (`F` of them,
the addresses of type `FORS_TREE` and height 0) to the nodes (`leaf_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR copyWords)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa (fld)
open VG.Proof.SlhDsa.X86_64.Levels (add_add sx_ofNat scr0 disj_scr toNat_at sub_scr bytesAt_congr callEntry_byte')

/-- The lanes `A` (`o = oA`) or `B`. -/
def Lanes (o st : Nat) : Prop := (o = 3296 ∧ st = 128) ∨ (o = 3808 ∧ st = 2208)

theorem Lanes.lo {o st : Nat} (h : Lanes o st) : 2400 ≤ o := by rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

theorem Lanes.hi {o st : Nat} (h : Lanes o st) : o + 4 * st ≤ 12640 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem Lanes.st {o st : Nat} (h : Lanes o st) : 128 ≤ st := by rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide

theorem Lanes.st_lt {o st : Nat} (h : Lanes o st) : st < 2 ^ 31 := by rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide

theorem Lanes.o_lt {o st : Nat} (h : Lanes o st) : o < 2 ^ 31 := by rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

section Call
variable {p : Params}

/-- `thashArgs` for the lanes at `o` of stride `st`, messages of `len` bytes. -/
theorem targs_ok (hn : p.n ≤ 32) {o st len : Nat} (hl : Lanes o st) (hlen : len < 2 ^ 31) {S : Addr} {t : State}
    (hbx : t.gpr .rbx = S) {Q : State → Prop}
    (k : ∀ u, u.gpr .rdi = at' S o → u.gpr .rsi = BitVec.ofNat 64 st →
      u.gpr .rdx = BitVec.ofNat 64 len → u.gpr .rcx = at' S (o + (p.n + 32)) → u.gpr .r8 = S →
      (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) →
      u.mem = t.mem → u.rd = t.rd → u.wr = t.wr → u.mxcsr = t.mxcsr → Q u) :
    WP isa (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ o st len)) t Q := by
  refine WP.mono_mx (by rfl) (Q := fun u => u.mxcsr = t.mxcsr → Q u) ?_ fun _ hq hmx => hq hmx
  simp only [Impl.SlhDsa.X86_64.thashArgs, Layout.msgOff]
  refine Proof.Sha3.X86_64.wp_mov fun u₁ v₁ => Proof.Sha3.X86_64.wp_addi fun u₂ v₂ =>
    Proof.Sha3.X86_64.wp_mov32i fun u₃ v₃ => Proof.Sha3.X86_64.wp_mov32i fun u₄ v₄ =>
    Proof.Sha3.X86_64.wp_mov fun u₅ v₅ => Proof.Sha3.X86_64.wp_addi fun u₆ v₆ =>
    Proof.Sha3.X86_64.wp_mov fun u₇ v₇ => WP.block_nil ?_
  have hA : o < 2 ^ 31 := hl.o_lt
  have h7 : u₇.gpr .rdi = at' S o := by
    rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.gpr, hbx, sx_ofNat hA]
  refine k u₇ h7 ?_ ?_ ?_ ?_ (fun g h1 h2 h3 h4 h5 => ?_) ?_ ?_ ?_
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := hl.st_lt; omega_using [this]
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hlen]
  · rw [v₇.other _ (by decide), v₆.gpr, v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.gpr, hbx, sx_ofNat hA, sx_ofNat (by omega_using [hn]), add_add]
  · rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hbx]
  · rw [v₇.other _ h5, v₆.other _ h4, v₅.other _ h4, v₄.other _ h3, v₃.other _ h2, v₂.other _ h1, v₁.other _ h1]
  · rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  · rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]

/-- The lanes and `work`, as the call narrows the regions to them. -/
abbrev callG (S : Addr) (o st : Nat) : List Region := [⟨at' S o, 4 * st⟩, ⟨S, workLen⟩]

/-- `thash4`'s precondition at the entry of the call after `thashArgs`, and its regions. -/
theorem t4g_entry (T : Thash4Impl p.n) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {stack : Nat}
    (hst : T.stack + 8 ≤ stack) (hs63 : stack < 2 ^ 63) {o st len : Nat} (hl : Lanes o st)
    (hpos : 0 < len) (hmod : len % 8 = 0) (hle : len ≤ st) {S : Addr} {t u : State}
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hrc : RcTable t.mem S)
    (h1 : u.gpr .rdi = at' S o) (h2 : u.gpr .rsi = BitVec.ofNat 64 st)
    (h3 : u.gpr .rdx = BitVec.ofNat 64 len) (h4 : u.gpr .rcx = at' S (o + (p.n + 32)))
    (h5 : u.gpr .r8 = S) (hg : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g)
    (hm : u.mem = t.mem) (hwr : u.wr = t.wr) :
    (thash4Contract p.n T.stack).pre (u.callEntry.withRegions [] (callG S o st)) ∧
      Covers ([] ++ callG S o st) (u.rd ++ u.wr) ∧ Covers (callG S o st) u.wr := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hlo := hl.lo
  have hhi := hl.hi
  have hst128 := hl.st
  have hstl := hl.st_lt
  have hsp : u.gpr .rsp = t.gpr .rsp := hg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hne : ∀ r : Reg, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r h => State.callEntry_gpr _ h
  have hstk8 : (below (u.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [hsp]; exact hstk.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have hcallee : (below (u.callEntry.gpr .rsp) T.stack).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [State.callEntry_rsp, hsp]
    exact hstk.sub_left (fun x hx => below_sub (sp := t.gpr .rsp) (a := T.stack + 8) (by omega_using [hst])
      (by omega_using [hs63]) x (below_callee _ _ x hx))
  have hret : (retR u.callEntry).Disjoint ⟨S, 2 ^ 16⟩ := by
    have : retR u.callEntry = below (u.gpr .rsp) 8 := by simp [retR, State.callEntry_rsp]
    rw [this]; exact hstk8
  have lanes_scr : Region.Sub ⟨at' S o, 4 * st⟩ ⟨S, 2 ^ 16⟩ := sub_scr S (by omega_using [hhi])
  have work_scr : Region.Sub ⟨S, workLen⟩ ⟨S, 2 ^ 16⟩ := Region.sub_prefix (by simp [workLen])
  have hcm : Frame [below (u.gpr .rsp) 8] u.mem u.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hgpr : ∀ r, r ≠ .rsp → (u.callEntry.withRegions [] (callG S o st)).gpr r = u.gpr r := fun r h => by
    rw [State.withRegions_gpr, hne _ h]
  have hstN : (BitVec.ofNat 64 st).toNat = st := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hstl])
  have hlen : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hle, hstl])
  have hpre : (thash4Contract p.n T.stack).pre (u.callEntry.withRegions [] (callG S o st)) := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.withRegions_wr, hgpr _ (by decide), hgpr _ (by decide), hgpr _ (by decide), h1, h2, h5, hstN]
    · rw [hgpr _ (by decide), hgpr _ (by decide), hgpr _ (by decide), h1, h2, h5, hstN]
      conv => rhs; rw [scr0 S]
      exact disj_scr S (Or.inr (by simp only [workLen]; omega_using [hlo])) (by omega_using [hhi])
        (by simp [workLen])
    · rw [hgpr _ (by decide), hgpr _ (by decide), h1, h2, hstN]
      exact hret.sub_right lanes_scr
    · rw [hgpr _ (by decide), h5]; exact hret.sub_right work_scr
    · simp only [State.withRegions_gpr]; rw [hne .rdi (by decide), hne .rsi (by decide), h1, h2, hstN]
      exact hcallee.sub_right lanes_scr
    · simp only [State.withRegions_gpr]; rw [hne .r8 (by decide), h5]; exact hcallee.sub_right work_scr
    · rw [hgpr _ (by decide), hgpr _ (by decide), h1, h2, hstN, toNat_at (by omega_using [hS, hhi])]
      omega_using [hS, hhi]
    · rw [hgpr _ (by decide), h5]; simp only [workLen]; omega_using [hS]
    · rw [hgpr _ (by decide), h3, hlen]; exact hpos
    · rw [hgpr _ (by decide), h3, hlen]; exact hmod
    · rw [hgpr _ (by decide), hgpr _ (by decide), h3, h2, hlen, hstN]; exact hle
    · rw [hgpr _ (by decide), hgpr _ (by decide), h4, h1, add_add]
    · rw [hgpr _ (by decide), h2, hstN]; omega_using [hn32, hst128]
    · rw [State.withRegions_mem, hgpr _ (by decide), h5]
      intro r hr k hk
      rw [← hrc r hr k hk, ← hm]
      refine hcm.readW (r := ⟨S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k), 8⟩) (w := 64)
        (Region.contains_self (S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k)) 8) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      exact (hstk8.sub_right (sub_scr S (by omega_using [hr, hk]))).symm
  have hw' : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [hwr]; exact hw
  have hcov : Covers (callG S o st) u.wr := Covers.of_sub fun r hr => by
    simp only [callG, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hw', o, rfl, by show o + 4 * st ≤ 2 ^ 16; omega_using [hhi]⟩
    · exact ⟨_, hw', 0, scr0 S, by simp [workLen]⟩
  exact ⟨hpre, by rw [List.nil_append]; exact Covers.right hcov, hcov⟩

/-- Lane `k` of the lanes at `o`. -/
abbrev laneAt (o st k : Nat) : Nat := o + st * k

/-- What a call of `thash4` from `t` gives. -/
structure T4Post (n : Nat) (S : Addr) (stack o st len : Nat) (t t' : State) : Prop where
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  cs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  mx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10
  out : ∀ k < 4, bytesAt t'.mem (at' S (laneAt o st k + n + 32)) n =
    Spec.Sha3.shake256 (bytesAt t.mem (at' S (laneAt o st k)) len) n
  frame : Frame ((List.range 4).map (fun k => (⟨at' S (laneAt o st k + n + 32), n⟩ : Region)) ++
    [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below (t.gpr .rsp) stack]) t.mem t'.mem

/-- A call of `T` on the lanes at `o`, messages of `len` bytes, from a state
whose `rbx` is `scratch` (`S`), with `stack` bytes below its stack pointer
for the call. -/
theorem t4g_ok (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {stack : Nat}
    (hst : T.stack + 8 ≤ stack) (hs63 : stack < 2 ^ 63) {o st len : Nat} (hl : Lanes o st)
    (hpos : 0 < len) (hmod : len % 8 = 0) (hle : len ≤ st) {S : Addr} {t : State}
    (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hrc : RcTable t.mem S) :
    WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code o st len) t
      (T4Post p.n S stack o st len t) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hhi := hl.hi
  have hstl := hl.st_lt
  unfold Impl.SlhDsa.X86_64.thashCall
  refine WP.seq (targs_ok hn32 hl (by omega_using [hle, hstl]) hbx fun u h1 h2 h3 h4 h5 hg hm hr hwr hmx₀ => ?_)
  have hsp : u.gpr .rsp = t.gpr .rsp := hg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hne : ∀ r : Reg, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r h => State.callEntry_gpr _ h
  have hstk8 : (below (u.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := by
    rw [hsp]; exact hstk.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have hcm : Frame [below (u.gpr .rsp) 8] u.mem u.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hstN : (BitVec.ofNat 64 st).toNat = st := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hstl])
  have hlen : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hle, hstl])
  obtain ⟨hpre, hcovl, hcov⟩ := t4g_entry T hn hst hs63 hl hpos hmod hle hw hS hstk hrc h1 h2 h3 h4 h5 hg hm hwr
  have hd : 8 * T.code.depth + 16 < 2 ^ 64 := by have := T.depth_le; omega_using [this]
  refine WP.call_mx T.verified.1 T.nosp hd hpre hcovl hcov
    fun s' hrd hwr' hcs hf _ ⟨s₂, hm₂, _, hpost⟩ hmx => ?_
  have hentry : ∀ q, q < 2 ^ 16 → u.callEntry.mem (at' S q) = t.mem (at' S q) := fun q hq => by
    rw [← hm]
    exact callEntry_byte' u hstk8 hq
  have hlane : ∀ k < 4, laneAt o st k + st ≤ o + 4 * st := fun k hk => by
    simp only [laneAt]
    have : st * k + st ≤ 4 * st := by rw [Nat.mul_comm st k, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
    omega_using [this]
  refine ⟨by rw [hrd, hr], by rw [hwr', hwr], fun r hr' => ?_, by rw [hmx, hmx₀], fun k hk => ?_, ?_⟩
  · have hne5 : r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr', hg r hne5.1 hne5.2.1 hne5.2.2.1 hne5.2.2.2.1 hne5.2.2.2.2]
  · have e := hpost.1 k hk
    simp only [outAt, msg, State.withRegions_gpr, State.withRegions_mem, hne .rcx (by decide), hne .rsi (by decide),
      hne .rdi (by decide), hne .rdx (by decide), h1, h2, h3, h4, hstN, hlen, hm₂] at e
    rw [add_add, show o + (p.n + 32) + k * st = laneAt o st k + p.n + 32 by
      simp only [laneAt]; rw [Nat.mul_comm k st]; omega_using [], add_add,
      show o + k * st = laneAt o st k by simp only [laneAt]; rw [Nat.mul_comm k st]] at e
    rw [e]
    congr 1
    refine bytesAt_congr fun i hi => ?_
    have hb : laneAt o st k + i < 2 ^ 16 := by have := hlane k hk; omega_using [this, hi, hle, hhi]
    rw [add_add]
    exact hentry (laneAt o st k + i) hb
  · have f1 : Frame ((List.range 4).map (fun k => (⟨at' S (laneAt o st k + p.n + 32), p.n⟩ : Region)) ++
        [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below (t.gpr .rsp) stack]) u.mem u.callEntry.mem :=
      hcm.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below (t.gpr .rsp) stack, by simp, by rw [hsp]; exact below_sub (by omega_using [hst]) (by omega_using [hs63])⟩
    have f2 := hpost.2
    simp only [thash4Changes, State.withRegions_gpr, State.withRegions_mem, hm₂] at f2
    refine (hm ▸ f1).trans (f2.sub fun r hr => ?_)
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
    · refine ⟨⟨at' S (laneAt o st k + p.n + 32), p.n⟩,
        List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), ?_⟩
      rw [outAt, State.withRegions_gpr, hne .rcx (by decide), hne .rsi (by decide), h4, h2, hstN, add_add,
        show o + (p.n + 32) + k * st = laneAt o st k + p.n + 32 by
          simp only [laneAt]; rw [Nat.mul_comm k st]; omega_using []]
      exact fun _ h => h
    · exact ⟨⟨S, 1600⟩, by simp, by rw [hne .r8 (by decide), h5]; exact fun _ h => h⟩
    · exact ⟨⟨at' S 2368, 32⟩, by simp, by rw [hne .r8 (by decide), h5]; exact fun _ h => h⟩
    · refine ⟨below (t.gpr .rsp) stack, by simp, ?_⟩
      rw [State.callEntry_rsp, hsp]
      exact fun x hx => below_sub (sp := t.gpr .rsp) (a := T.stack + 8) (by omega_using [hst]) (by omega_using [hs63]) x
        (below_callee _ _ x hx)

end Call

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `cmp r64, imm32`, setting ZF and CF. -/
theorem wp_cmpiC {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

/-- `and r64, imm32`. -/
theorem wp_andi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Proof.Sha3.X86_64.Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (Proof.Sha3.X86_64.Upd.flags _ _ _ _ _ _))

/-- `or r64, r64`. -/
theorem wp_orr {d r : Reg} (k : ∀ s', Proof.Sha3.X86_64.Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (Proof.Sha3.X86_64.Upd.flags _ _ _ _ _ _))

/-- `xor r64, r64`. -/
theorem wp_xorr {d r : Reg} (k : ∀ s', Proof.Sha3.X86_64.Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (Proof.Sha3.X86_64.Upd.flags _ _ _ _ _ _))

/-- `add r64, [m]`. -/
theorem wp_addm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Proof.Sha3.X86_64.Upd s s' d (s.gpr d + s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.mem m) :: is)) s Q := by
  refine Proof.Sha3.X86_64.WP.cons ?_ (k _ (Proof.Sha3.X86_64.Upd.flags s d (s.gpr d + s.mem.readW a 64)
    (2 ^ 64 ≤ (s.gpr d).toNat + (s.mem.readW a 64).toNat)
    (addOverflow (s.gpr d) (s.mem.readW a 64) (s.gpr d + s.mem.readW a 64)) _))
  simp [exec, execAlu, readSrc, State.load64, ha, hin]

end

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some (!b) := by
  show s.zf.map (!·) = _; rw [h]; rfl

/-- The blocks of a `flatMap` over `range K`, one invariant at each. -/
theorem wp_flatMap {f : Nat → List Instr} {P : Nat → State → Prop} :
    ∀ (K : Nat) {s : State}, P 0 s → (∀ j < K, ∀ t, P j t → WP isa (.block (f j)) t (P (j + 1))) →
      WP isa (.block ((List.range K).flatMap f)) s (P K)
  | 0, _, h0, _ => WP.block_nil h0
  | K + 1, _, h0, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (wp_flatMap K h0 fun j hj => hs j (by omega_using [hj])) fun t ht =>
      hs K (by omega_using []) t ht)

/-! ## Bytes -/

theorem bytesAt_split (m : Mem) (S : Addr) (a x y : Nat) :
    bytesAt m (at' S a) (x + y) = bytesAt m (at' S a) x ++ bytesAt m (at' S (a + x)) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Levels.add_add, Nat.add_assoc]

/-- A byte of `scratch` that a frame of regions of `scratch` leaves. -/
theorem keepS {rs : List Region} {m m' : Mem} {S : Addr} (hf : Frame rs m m') {q : Nat}
    (h : ∀ r ∈ rs, Region.Disjoint ⟨at' S q, 1⟩ r) : m' (at' S q) = m (at' S q) := by
  have e := hf.bytes (R := ⟨at' S q, 1⟩) h (by show 1 ≤ 2 ^ 64; decide) (show 0 < 1 by decide)
  simpa using e

/-- The bytes of `scratch` that a frame leaves. -/
theorem keepSB {rs : List Region} {m m' : Mem} {S : Addr} (hf : Frame rs m m') {q l : Nat}
    (h : ∀ r ∈ rs, Region.Disjoint ⟨at' S q, l⟩ r) (hl : l ≤ 2 ^ 64) : bytesAt m' (at' S q) l = bytesAt m (at' S q) l :=
  bytesAt_frame hf h hl

/-- A word of `scratch` that a frame leaves. -/
theorem keepSW {rs : List Region} {m m' : Mem} {S : Addr} (hf : Frame rs m m') {q : Nat}
    (h : ∀ r ∈ rs, Region.Disjoint ⟨at' S q, 8⟩ r) : m'.readW (at' S q) 64 = m.readW (at' S q) 64 :=
  hf.readW (r := ⟨at' S q, 8⟩) (Region.contains_self _ _) h (by decide)

/-- Parts of `scratch` that do not overlap. -/
theorem dS (S : Addr) {o l o' l' : Nat} (h : o + l ≤ o' ∨ o' + l' ≤ o) (h₁ : o + l ≤ 2 ^ 16)
    (h₂ : o' + l' ≤ 2 ^ 16) : Region.Disjoint ⟨at' S o, l⟩ ⟨at' S o', l'⟩ :=
  Levels.disj_scr S h h₁ h₂

/-- The bytes of `scratch` that a frame of one region of `scratch` leaves. -/
theorem keep1 {m m' : Mem} {S : Addr} {o l q l' : Nat} (hf : Frame [⟨at' S o, l⟩] m m') (h : q + l' ≤ o ∨ o + l ≤ q)
    (h₁ : q + l' ≤ 2 ^ 16) (h₂ : o + l ≤ 2 ^ 16) : bytesAt m' (at' S q) l' = bytesAt m (at' S q) l' :=
  keepSB hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS S h h₁ h₂)
    (by omega_using [h₁])

/-! ## The lanes for the private key values -/

theorem laneA_eq (k : Nat) : Layout.laneA k = 3296 + 128 * k := rfl

/-- What lane `k`'s address and message are after `leafAdrs 6 k` and the
copy of `SK.seed`. -/
structure LaneP (n : Nat) (S : Addr) (t t' : State) (k ty kp x : Nat) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .r11 → t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  fields : bytesAt t'.mem (at' S (Layout.laneA k + n + 16)) 16 =
    toByte ty 4 ++ (toByte kp 4 ++ (toByte 0 4 ++ toByte x 4))
  msg : bytesAt t'.mem (at' S (Layout.laneA k + n + 32)) n = bytesAt t.mem (at' S Layout.oSkSeed) n
  frame : Frame [⟨at' S (Layout.laneA k + n + 16), 16 + n⟩] t.mem t'.mem

/-- Lane `k` for leaf `x + k` (`x` in `r10`), the key pair `kp` (`r12`), the
type `ty`; its message `SK.seed`. -/
theorem lane_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {k ty x : Nat} {KP : BitVec 64}
    {t : State} (hk : k < 4) (hty : ty < 2 ^ 31) (hbx : t.gpr .rbx = S) (h10 : t.gpr .r10 = BitVec.ofNat 64 x)
    (hx : x + k < 2 ^ 32) (h12 : t.gpr .r12 = KP) (hKP : KP.toNat < 2 ^ 32) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) :
    WP isa (.block (leafAdrs ⟨p.n, p.len⟩ ty k ++
        copyWords .rbx (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) .rbx Layout.oSkSeed (p.n / 8))) t
      fun t' => LaneP p.n S t t' k ty KP.toNat (x + k) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hla := laneA_eq k
  have hsk : Layout.oSkSeed = 3168 := rfl
  have hbase : ∀ d, t.gpr .rbx + BitVec.ofNat 64 d = at' S d := fun d => by rw [hbx]
  simp only [leafAdrs, Layout.adrsOff, Layout.msgOff, List.append_assoc]
  refine setField_ok (by decide) hty (by rw [hbase]; exact Levels.in_scr hw (by omega_using [hla, hk, hn32]))
    fun t₁ f₁ => ?_
  have hb₁ : t₁.gpr .rbx = S := by rw [f₁.gpr _ (by decide), hbx]
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₁.wr := by rw [f₁.wr]; exact hw
  refine setFieldR_ok (r := .r12) (by decide) (by rw [f₁.gpr _ (by decide), h12]; exact hKP)
    (by rw [hb₁]; exact Levels.in_scr hw₁ (by omega_using [hla, hk, hn32])) fun t₂ f₂ => ?_
  have hb₂ : t₂.gpr .rbx = S := by rw [f₂.gpr _ (by decide), hb₁]
  have hw₂ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₂.wr := by rw [f₂.wr]; exact hw₁
  refine setField_ok (by decide) (by decide : 0 < 2 ^ 31) (by rw [hb₂]; exact Levels.in_scr hw₂ (by omega_using [hla, hk, hn32]))
    fun t₃ f₃ => ?_
  refine Proof.Sha3.X86_64.wp_mov fun t₄ u₄ => Proof.Sha3.X86_64.wp_addi fun t₅ u₅ => ?_
  have hb₅ : t₅.gpr .rbx = S := by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₃.gpr _ (by decide), hb₂]
  have hw₅ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₅.wr := by rw [u₅.wr, u₄.wr, f₃.wr]; exact hw₂
  have h11 : (t₅.gpr .r11).toNat = x + k := by
    rw [u₅.gpr, u₄.gpr, f₃.gpr _ (by decide), f₂.gpr _ (by decide), f₁.gpr _ (by decide), h10,
      Levels.sx_ofNat (by omega_using [hk]), BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hx])]
  refine setFieldR_ok (r := .r11) (by decide) (by rw [h11]; exact hx)
    (by rw [hb₅]; exact Levels.in_scr hw₅ (by omega_using [hla, hk, hn32])) fun t₆ f₆ => ?_
  have hb₆ : t₆.gpr .rbx = S := by rw [f₆.gpr _ (by decide), hb₅]
  have hw₆ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₆.wr := by rw [f₆.wr]; exact hw₅
  refine WP.mono (Levels.copy_ok (S := S) (a := 0) (b := 0) (d₁ := Layout.oSkSeed) (d₂ := Layout.laneA k + p.n + 32)
    (by decide) (by decide) (p.n / 8) t₆ (by rw [hb₆]; exact Levels.scr0 S) (by rw [hb₆]; exact Levels.scr0 S) hw₆
    (by omega_using [e8, hsk, hn32]) (by omega_using [e8, hla, hk, hn32]) (by omega_using [e8, hla, hsk, hn32]))
    fun t' ⟨g', r', w', c', f'⟩ => ?_
  rw [e8, Nat.zero_add, Nat.zero_add] at c'
  rw [e8, Nat.zero_add] at f'
  simp only [hb₁, hb₂, hb₅, hbx] at f₁ f₂ f₃ f₆
  have hm₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  have fr₁ := f₁.frame
  have fr₂ := f₂.frame
  have fr₃ := f₃.frame
  have fr₆ := f₆.frame
  have hL := Nat.mul_le_mul_left 128 (show k ≤ 3 by omega_using [hk])
  have hb16 : Layout.laneA k + p.n + 16 + 16 + p.n ≤ 2 ^ 16 := by omega_using [hla, hL, hn32]
  have b₁ := f₁.bytes
  have b₂ := f₂.bytes
  have b₃ := f₃.bytes
  have b₆ := f₆.bytes
  try simp only [hbx, hb₁, hb₂, hb₅] at b₁ b₂ b₃ b₆
  rw [f₁.gpr _ (by decide), h12] at b₂
  rw [h11] at b₆
  -- each field, through the writes after it
  have c₀ : bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16)) 4 = toByte ty 4 := by
    rw [keep1 f' (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [e8, hb16]),
      keep1 fr₆ (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]), hm₅,
      keep1 fr₃ (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]),
      keep1 fr₂ (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]), b₁]
  have c₁ : bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16 + 4)) 4 = toByte KP.toNat 4 := by
    rw [keep1 f' (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [e8, hb16]),
      keep1 fr₆ (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]), hm₅,
      keep1 fr₃ (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]),
      show Layout.laneA k + p.n + 16 + 4 = Layout.laneA k + p.n + 20 by omega_using [], b₂]
  have c₂ : bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16 + 8)) 4 = toByte 0 4 := by
    rw [keep1 f' (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [e8, hb16]),
      keep1 fr₆ (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]), hm₅,
      show Layout.laneA k + p.n + 16 + 8 = Layout.laneA k + p.n + 24 by omega_using [], b₃]
  have c₃ : bytesAt t'.mem (at' S (Layout.laneA k + p.n + 16 + 12)) 4 = toByte (x + k) 4 := by
    rw [keep1 f' (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [e8, hb16]),
      show Layout.laneA k + p.n + 16 + 12 = Layout.laneA k + p.n + 28 by omega_using [], b₆]
  -- `SK.seed`, as the writes before the copy left it
  have hsk' : bytesAt t₆.mem (at' S Layout.oSkSeed) p.n = bytesAt t.mem (at' S Layout.oSkSeed) p.n := by
    rw [keep1 fr₆ (.inl (by omega_using [hla, hsk, hn32])) (by omega_using [hsk, hn32]) (by omega_using [hb16]), hm₅,
      keep1 fr₃ (.inl (by omega_using [hla, hsk, hn32])) (by omega_using [hsk, hn32]) (by omega_using [hb16]),
      keep1 fr₂ (.inl (by omega_using [hla, hsk, hn32])) (by omega_using [hsk, hn32]) (by omega_using [hb16]),
      keep1 fr₁ (.inl (by omega_using [hla, hsk, hn32])) (by omega_using [hsk, hn32]) (by omega_using [hb16])]
  refine ⟨fun g h1 h2 => ?_, by rw [r', f₆.rd, u₅.rd, u₄.rd, f₃.rd, f₂.rd, f₁.rd],
    by rw [w', f₆.wr, u₅.wr, u₄.wr, f₃.wr, f₂.wr, f₁.wr], ?_, ?_, ?_⟩
  · rw [g' _ h1, f₆.gpr _ h1, u₅.other _ h2, u₄.other _ h2, f₃.gpr _ h1, f₂.gpr _ h1, f₁.gpr _ h1]
  · rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, bytesAt_split, bytesAt_split, bytesAt_split,
      show Layout.laneA k + p.n + 16 + 4 + 4 = Layout.laneA k + p.n + 16 + 8 by omega_using [],
      show Layout.laneA k + p.n + 16 + 8 + 4 = Layout.laneA k + p.n + 16 + 12 by omega_using [], c₀, c₁, c₂, c₃]
  · rw [← hsk']
    refine bytesAt_ext fun i hi => ?_
    rw [Levels.add_add, Levels.add_add]
    exact (c' i hi)
  · have sub : ∀ o l, Layout.laneA k + p.n + 16 ≤ o → o + l ≤ Layout.laneA k + p.n + 16 + (16 + p.n) →
        ∀ r ∈ [(⟨at' S o, l⟩ : Region)], ∃ r' ∈ [(⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩ : Region)],
          Region.Sub r r' := fun o l h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S h₁ h₂⟩
    exact (fr₁.sub (sub _ _ (by omega_using []) (by omega_using []))).trans
      ((fr₂.sub (sub _ _ (by omega_using []) (by omega_using []))).trans
      ((hm₅ ▸ fr₃.sub (sub _ _ (by omega_using []) (by omega_using []))).trans
      ((fr₆.sub (sub _ _ (by omega_using []) (by omega_using []))).trans
      (f'.sub (sub _ _ (by omega_using []) (by omega_using [e8]))))))

/-- Variable `i` of frame 2. -/
theorem oVar2 (i : Nat) : Layout.oVar 2 i = 2704 + 8 * i := rfl

/-- The lanes' fields and messages, which the lanes for the private key
values write. -/
abbrev laneRs (n : Nat) (S : Addr) : List Region :=
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + n + 16), 16 + n⟩ : Region)

/-- What the lanes for the private key values are, after the first block of
`leafBody`, for the leaves `x` to `x + 3`. -/
structure LanesP (n : Nat) (S : Addr) (t t' : State) (kp x : Nat) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .r10 → g ≠ .r11 → t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  fields : ∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + n + 16)) 16 =
    toByte 6 4 ++ (toByte kp 4 ++ (toByte 0 4 ++ toByte (x + k) 4))
  msg : ∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + n + 32)) n = bytesAt t.mem (at' S Layout.oSkSeed) n
  frame : Frame (laneRs n S) t.mem t'.mem

/-- The lanes of two different `k` do not overlap. -/
theorem lane_disj {k k' : Nat} (hk : k < 4) (hk' : k' < 4) (hne : k ≠ k') {o l o' l' : Nat}
    (h₁ : o + l ≤ 128) (h₂ : o' + l' ≤ 128) (S : Addr) :
    Region.Disjoint ⟨at' S (Layout.laneA k + o), l⟩ ⟨at' S (Layout.laneA k' + o'), l'⟩ := by
  rw [laneA_eq, laneA_eq]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact dS S (.inl (by omega_using [h, h₁, h₂])) (by omega_using [hk, h₁]) (by omega_using [hk', h₂])
  · exact dS S (.inr (by omega_using [h, h₁, h₂])) (by omega_using [hk, h₁]) (by omega_using [hk', h₂])

/-- The first block of `leafBody`: the lanes for the private key values of the
leaves `V4 + U2 + J` to that plus 3 (frame 2's variables 4, 2 and 3). -/
theorem lanesA_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {KP : BitVec 64} {V4 U2 J : Nat}
    {t : State} (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = KP) (hKP : KP.toNat < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (h4 : t.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4)
    (h2 : t.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2)
    (h3 : t.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 J) (hX : V4 + U2 + J + 4 ≤ 2 ^ 32) :
    WP isa (.block (([.mov .r10 (.mem (var 4)), .alu .add .r10 (.mem (var 2)), .alu .add .r10 (.mem (var 3))] : List Instr) ++
        (List.range 4).flatMap (fun k => leafAdrs ⟨p.n, p.len⟩ 6 k ++
          copyWords .rbx (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) .rbx Layout.oSkSeed (p.n / 8)))) t
      fun t' => LanesP p.n S t t' KP.toNat (V4 + U2 + J) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hsk : Layout.oSkSeed = 3168 := rfl
  have hin : ∀ i, i < 9 → InRegions (t.rd ++ t.wr) (at' S (Layout.oVar 2 i)) 8 := fun i hi =>
    Levels.in_scr' hw (by rw [oVar2]; omega_using [hi])
  simp only [List.cons_append, List.nil_append]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 4)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (hin 4 (by decide)) fun t₁ u₁ => ?_
  refine wp_addm (a := at' S (Layout.oVar 2 2)) (by rw [var, Proof.Sha3.X86_64.ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.rd, u₁.wr]; exact hin 2 (by decide)) fun t₂ u₂ => ?_
  refine wp_addm (a := at' S (Layout.oVar 2 3))
    (by rw [var, Proof.Sha3.X86_64.ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 3 (by decide)) fun t₃ u₃ => ?_
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have h10 : t₃.gpr .r10 = BitVec.ofNat 64 (V4 + U2 + J) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, h4, h2, h3, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  have hg₃ : ∀ g, g ≠ .r10 → t₃.gpr g = t.gpr g := fun g h => by rw [u₃.other _ h, u₂.other _ h, u₁.other _ h]
  let P : Nat → State → Prop := fun c u =>
    (∀ g, g ≠ .rax → g ≠ .r11 → u.gpr g = t₃.gpr g) ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
    (∀ k < c, bytesAt u.mem (at' S (Layout.laneA k + p.n + 16)) 16 =
      toByte 6 4 ++ (toByte KP.toNat 4 ++ (toByte 0 4 ++ toByte (V4 + U2 + J + k) 4))) ∧
    (∀ k < c, bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n = bytesAt t.mem (at' S Layout.oSkSeed) p.n) ∧
    Frame (laneRs p.n S) t.mem u.mem
  have hP := wp_flatMap (P := P) 4 (s := t₃) ⟨fun _ _ _ => rfl, by rw [u₃.rd, u₂.rd, u₁.rd],
      by rw [u₃.wr, u₂.wr, u₁.wr], fun _ h => absurd h (by omega_using []), fun _ h => absurd h (by omega_using []),
      hm₃ ▸ Frame.refl _ _⟩ fun c hc u ⟨g, r, w, fl, ms, fr⟩ => by
    refine WP.mono (lane_ok hn hc (by decide : 6 < 2 ^ 31) (by rw [g _ (by decide) (by decide), hg₃ _ (by decide), hbx])
      (by rw [g _ (by decide) (by decide), h10]) (by omega_using [hc, hX])
      (by rw [g _ (by decide) (by decide), hg₃ _ (by decide), h12]) hKP (by rw [w]; exact hw)) fun u' l => ?_
    have hla := laneA_eq c
    have hL := Nat.mul_le_mul_left 128 (show c ≤ 3 by omega_using [hc])
    -- the lane's region, and the others'
    have dk : ∀ k < 4, k ≠ c → ∀ o l, o + l ≤ 128 →
        ∀ r ∈ [(⟨at' S (Layout.laneA c + p.n + 16), 16 + p.n⟩ : Region)], Region.Disjoint ⟨at' S (Layout.laneA k + o), l⟩ r :=
      fun k hk hne o l hl r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [show Layout.laneA c + p.n + 16 = Layout.laneA c + (p.n + 16) by omega_using []]
        exact lane_disj hk hc hne hl (by omega_using [hn32]) S
    refine ⟨fun g' h1 h2 => by rw [l.gpr _ h1 h2, g _ h1 h2], by rw [l.rd, r], by rw [l.wr, w], fun k hk => ?_,
      fun k hk => ?_, ?_⟩
    · by_cases e : k = c
      · subst e; exact l.fields
      · rw [show Layout.laneA k + p.n + 16 = Layout.laneA k + (p.n + 16) by omega_using [],
          keepSB l.frame (dk k (by omega_using [hk, hc]) e _ _ (by omega_using [hn32])) (by decide),
          ← show Layout.laneA k + p.n + 16 = Layout.laneA k + (p.n + 16) by omega_using []]
        exact fl k (by omega_using [hk, e])
    · by_cases e : k = c
      · subst e
        rw [l.msg]
        refine keepSB fr (fun r hr => ?_) (by omega_using [hn32])
        simp only [laneRs, List.mem_map, List.mem_range] at hr
        obtain ⟨k', hk', rfl⟩ := hr
        exact dS S (.inl (by rw [laneA_eq]; omega_using [hsk, hn32])) (by omega_using [hsk, hn32])
          (by rw [laneA_eq]; have := Nat.mul_le_mul_left 128 (show k' ≤ 3 by omega_using [hk']); omega_using [this, hn32])
      · rw [show Layout.laneA k + p.n + 32 = Layout.laneA k + (p.n + 32) by omega_using [],
          keepSB l.frame (dk k (by omega_using [hk, hc]) e _ _ (by omega_using [hn32])) (by omega_using [hn32]),
          ← show Layout.laneA k + p.n + 32 = Layout.laneA k + (p.n + 32) by omega_using []]
        exact ms k (by omega_using [hk, e])
    · exact fr.trans (l.frame.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
  refine WP.mono hP fun t' ⟨g, r, w, fl, ms, fr⟩ => ⟨fun g' h1 h2 h3 => by rw [g _ h1 h3, hg₃ _ h2], r, w,
    fun k hk => by rw [fl k hk, Nat.add_assoc (V4 + U2) J k], ms, fr⟩

/-! ## The capture of the private key value -/

/-- The masked XOR of `W` words of a lane (at `S + D`, `rbx = S`) into those at
`au` (`rsi`): the lane's bytes if the mask in `rdi` is all ones (`c`), kept
if it is zero. -/
theorem xorLane_ok {c : Prop} [Decidable c] {S au : Addr} {D : Nat} :
    ∀ (W : Nat) (s : State), s.gpr .rbx = S → s.gpr .rsi = au →
      s.gpr .rdi = (if c then BitVec.allOnes 64 else 0) → (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr → D + 8 * W ≤ 2 ^ 16 →
      (∀ w < W, InRegions s.wr (au + BitVec.ofNat 64 (8 * w)) 8) →
      Region.Disjoint ⟨at' S D, 8 * W⟩ ⟨au, 8 * W⟩ → 8 * W ≤ 2 ^ 64 →
      WP isa (.block ((List.range W).flatMap fun w =>
          [.mov .rax (.mem (Impl.Sha3.X86_64.at_ .rbx (D + 8 * w))), .alu .and .rax (.reg .rdi),
            .alu .xor .rax (.mem (Impl.Sha3.X86_64.at_ .rsi (8 * w))), .store (Impl.Sha3.X86_64.at_ .rsi (8 * w)) .rax]))
        s (fun s' => (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
          (∀ j < 8 * W, s'.mem (au + BitVec.ofNat 64 j) =
            (if c then s.mem (at' S (D + j)) else 0) ^^^ s.mem (au + BitVec.ofNat 64 j)) ∧
          Frame [⟨au, 8 * W⟩] s.mem s'.mem) := by
  intro W
  induction W with
  | zero =>
    intro s _ _ _ _ _ _ _ _
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun j hj => absurd hj (by omega_using []), Frame.refl _ _⟩
  | succ W ih =>
    intro s h₁ h₂ h₃ hS hD hout hd hW
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih s h₁ h₂ h₃ hS (by omega_using [hD])
      (fun w hw => hout w (by omega_using [hw])) (hd.sub_left (Region.sub_prefix (by omega_using []))
        |>.sub_right (Region.sub_prefix (by omega_using []))) (by omega_using [hW]))
      fun s₁ ⟨g₁, r₁, w₁, c₁, f₁⟩ => ?_)
    refine Proof.Sha3.X86_64.wp_movm (a := at' S (D + 8 * W))
      (by rw [Proof.Sha3.X86_64.ea_at, g₁ _ (by decide), h₁]) (by rw [r₁, w₁]; exact Levels.in_scr' hS (by omega_using [hD]))
      fun s₂ u₂ => ?_
    refine Proof.Sha3.X86_64.wp_and fun s₃ u₃ => ?_
    refine Proof.Sha3.X86_64.wp_xorm (a := au + BitVec.ofNat 64 (8 * W))
      (by rw [Proof.Sha3.X86_64.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h₂])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, r₁, w₁]
          obtain ⟨r, hr, hc⟩ := hout W (by omega_using [])
          exact ⟨r, List.mem_append_right _ hr, hc⟩) fun s₄ u₄ => ?_
    refine Proof.Sha3.X86_64.wp_store (a := au + BitVec.ofNat 64 (8 * W))
      (by rw [Proof.Sha3.X86_64.ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide), h₂])
      (by rw [u₄.wr, u₃.wr, u₂.wr, w₁]; exact hout W (by omega_using [])) fun s₅ g₅ m₅ r₅ w₅ => WP.block_nil ?_
    have hm : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have hrdi : s₂.gpr .rdi = (if c then BitVec.allOnes 64 else 0) := by rw [u₂.other _ (by decide), g₁ _ (by decide), h₃]
    have hnd : ∀ j < 8 * (W + 1), s₁.mem (at' S (D + j)) = s.mem (at' S (D + j)) := fun j hj => by
      have e := Frame.bytes (R := ⟨at' S D, 8 * (W + 1)⟩) f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd.sub_right (Region.sub_prefix (by omega_using []))) (by omega_using [hW]) hj
      rwa [Levels.add_add] at e
    have hau : ∀ j, 8 * W ≤ j → j < 8 * (W + 1) → s₁.mem (au + BitVec.ofNat 64 j) = s.mem (au + BitVec.ofNat 64 j) := by
      intro j h1 h2
      refine f₁ _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hc
      rw [Nat.mod_eq_of_lt (by omega_using [hW, h2])] at hc
      omega_using [hc, h1]
    refine ⟨fun g hg => by rw [g₅, u₄.other _ hg, u₃.other _ hg, u₂.other _ hg, g₁ _ hg], by rw [r₅, u₄.rd, u₃.rd, u₂.rd, r₁],
      by rw [w₅, u₄.wr, u₃.wr, u₂.wr, w₁], fun j hj => ?_, ?_⟩
    · rw [m₅, hm, Levels.byte_write8' _ _ (by omega_using [hW]) (by omega_using [hW, hj])]
      split
      · rename_i h
        have e1 : 8 * W + (j - 8 * W) = j := by omega_using [h]
        have hm3 : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
        rw [u₄.gpr, u₃.gpr, u₂.gpr, hrdi, Levels.and_mask, BitVec.extractLsb'_xor, hm3]
        rw [show au + BitVec.ofNat 64 (8 * W) = au + BitVec.ofNat 64 (8 * W) from rfl,
          VG.X86_64.byte_readW _ _ (by omega_using [h]), Levels.add_add, e1, hau j h.1 h.2]
        by_cases hc : c
        · rw [ite_eq_left hc, ite_eq_left hc, VG.X86_64.byte_readW _ _ (by omega_using [h]), Levels.add_add,
            show D + 8 * W + (j - 8 * W) = D + j by omega_using [h], hnd j hj]
        · rw [ite_eq_right hc, ite_eq_right hc]; simp
      · rename_i h
        rw [c₁ j (by omega_using [h, hj])]
    · rw [m₅, hm]
      have hsub : Frame [⟨au, 8 * (W + 1)⟩] s.mem s₁.mem := Frame.sub f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
      exact hsub.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hW]))

/-- The mask's value: `x ⊕ i = 0` iff `x = i`. -/
theorem xor_zero_iff {x i : Nat} (hx : x < 2 ^ 32) (hi : i < 2 ^ 32) :
    BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 i = 0 ↔ x = i := by
  constructor
  · intro h
    have e := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h)
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hx]),
      Nat.mod_eq_of_lt (by omega_using [hi])] at e
  · intro h; rw [h]; exact BitVec.xor_self

theorem xor_lt {x i : Nat} (hx : x < 2 ^ 32) (hi : i < 2 ^ 32) :
    (BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 i).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hx]),
    Nat.mod_eq_of_lt (by omega_using [hi])]
  have := Nat.xor_lt_two_pow hx hi
  omega_using [this]

/-- `captureSk k`: lane `k`'s message XORed into the `n` bytes at `au`
(`rsi`) if `C + k = idx` (`rdx = C`, `r13 = idx`). -/
theorem capture_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S au : Addr} {k C idx : Nat} {t : State}
    (hk : k < 4) (hbx : t.gpr .rbx = S) (hdx : t.gpr .rdx = BitVec.ofNat 64 C) (h13 : t.gpr .r13 = BitVec.ofNat 64 idx)
    (hsi : t.gpr .rsi = au) (hC : C + 4 < 2 ^ 32) (hidx : idx < 2 ^ 32) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hout : ∀ w < p.n / 8, InRegions t.wr (au + BitVec.ofNat 64 (8 * w)) 8)
    (hd : Region.Disjoint ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ ⟨au, p.n⟩) :
    WP isa (.block (captureSk ⟨p.n, p.len⟩ k)) t fun t' =>
      (∀ g, g ≠ .rax → g ≠ .rdi → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ j < p.n, t'.mem (au + BitVec.ofNat 64 j) =
        (if C + k = idx then t.mem (at' S (Layout.laneA k + p.n + 32 + j)) else 0) ^^^ t.mem (au + BitVec.ofNat 64 j)) ∧
      Frame [⟨au, p.n⟩] t.mem t'.mem := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hla := laneA_eq k
  have hL := Nat.mul_le_mul_left 128 (show k ≤ 3 by omega_using [hk])
  simp only [captureSk, List.cons_append, List.nil_append]
  refine Proof.Sha3.X86_64.wp_mov fun t₁ u₁ => Proof.Sha3.X86_64.wp_addi fun t₂ u₂ =>
    Proof.Sha3.X86_64.wp_xor fun t₃ u₃ => Proof.Sha3.X86_64.wp_subi fun t₄ u₄ _ =>
    Levels.wp_shr (by decide) (by decide) fun t₅ u₅ => Proof.Sha3.X86_64.wp_mov32i fun t₆ u₆ =>
    Levels.wp_sub fun t₇ u₇ => ?_
  have hx : t₃.gpr .rax = BitVec.ofNat 64 (C + k) ^^^ BitVec.ofNat 64 idx := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, u₂.other _ (by decide : Reg.r13 ≠ .rax), u₁.other _ (by decide : Reg.r13 ≠ .rax), hdx, h13,
      Levels.sx_ofNat (by omega_using [hk]), BitVec.ofNat_add_ofNat]
  have hrdi : t₇.gpr .rdi = if C + k = idx then BitVec.allOnes 64 else 0 := by
    rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide : Reg.rax ≠ .rdi), u₅.gpr, u₄.gpr, hx,
      show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide,
      show (BitVec.setWidth 64 (0 : BitVec 32)) = (0 : BitVec 64) from rfl, Levels.mask_eq (xor_lt (by omega_using [hC, hk]) hidx)]
    by_cases h : C + k = idx
    · rw [ite_eq_left h, ite_eq_left ((xor_zero_iff (by omega_using [hC, hk]) hidx).mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun e => h ((xor_zero_iff (by omega_using [hC, hk]) hidx).mp e))]
  have hg₇ : ∀ g, g ≠ .rax → g ≠ .rdi → t₇.gpr g = t.gpr g := fun g h1 h2 => by
    rw [u₇.other _ h2, u₆.other _ h2, u₅.other _ h1, u₄.other _ h1, u₃.other _ h1, u₂.other _ h1, u₁.other _ h1]
  have hm₇ : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hr₇ : t₇.rd = t.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hw₇ : t₇.wr = t.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine WP.mono (xorLane_ok (c := C + k = idx) (S := S) (au := au)
    (D := Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) (p.n / 8) t₇
    (by rw [hg₇ _ (by decide) (by decide), hbx]) (by rw [hg₇ _ (by decide) (by decide), hsi]) hrdi
    (by rw [hw₇]; exact hw) (by simp only [Layout.msgOff]; omega_using [e8, hla, hL, hn32])
    (fun w hw' => by rw [hw₇]; exact hout w hw')
    (by simp only [Layout.msgOff]; rw [e8, show Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 by omega_using []]
        exact hd) (by omega_using [e8, hn32])) fun t' ⟨g', r', w', c', f'⟩ => ?_
  rw [e8] at c' f'
  refine ⟨fun g h1 h2 => by rw [g' _ h1, hg₇ _ h1 h2], by rw [r', hr₇], by rw [w', hw₇], fun j hj => ?_, hm₇ ▸ f'⟩
  rw [c' j hj, hm₇]
  simp only [Layout.msgOff]
  rw [show Layout.laneA k + (p.n + 32) + j = Layout.laneA k + p.n + 32 + j by omega_using []]

theorem zero_xor8 (x : Byte) : (0 : Byte) ^^^ x = x := BitVec.zero_xor

/-- The type fields of the lanes `A`. -/
abbrev typeRs (n : Nat) (S : Addr) : List Region :=
  (List.range 4).map fun k => (⟨at' S (Layout.laneA k + n + 16), 4⟩ : Region)

/-- What the second block of `leafBody` does: the private key value of the
index `idx`, if it is one of the leaves `C` to `C + 3` of the subtree,
XORed into the signature's at `AU`; the lanes' type `FORS_TREE`. -/
structure CapP (n : Nat) (S AU : Addr) (t t' : State) (C idx : Nat) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sk : ∀ j < n, t'.mem (AU + BitVec.ofNat 64 j) =
    if C ≤ idx ∧ idx < C + 4 then t.mem (at' S (Layout.laneA (idx - C) + n + 32 + j)) ^^^ t.mem (AU + BitVec.ofNat 64 j)
    else t.mem (AU + BitVec.ofNat 64 j)
  ty : ∀ k < 4, bytesAt t'.mem (at' S (Layout.laneA k + n + 16)) 4 = toByte 3 4
  frame : Frame (⟨AU, n⟩ :: typeRs n S) t.mem t'.mem

theorem capB_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S AU : Addr} {U2 J idx : Nat} {t : State}
    (hbx : t.gpr .rbx = S) (h13 : t.gpr .r13 = BitVec.ofNat 64 idx) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (h1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (h2 : t.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2)
    (h3 : t.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 J) (hC : U2 + J + 4 < 2 ^ 32)
    (hidx : idx < 2 ^ 32) (hout : ∀ w < p.n / 8, InRegions t.wr (AU + BitVec.ofNat 64 (8 * w)) 8)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) :
    WP isa (.block (([.mov .rsi (.mem (var 1)), .mov .rdx (.mem (var 2)), .alu .add .rdx (.mem (var 3))] : List Instr) ++
        (List.range 4).flatMap (captureSk ⟨p.n, p.len⟩) ++
        (List.range 4).flatMap (fun k => setField .rbx (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 3))) t
      fun t' => CapP p.n S AU t t' (U2 + J) idx := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hin : ∀ i, i < 9 → InRegions (t.rd ++ t.wr) (at' S (Layout.oVar 2 i)) 8 := fun i hi =>
    Levels.in_scr' hw (by rw [oVar2]; omega_using [hi])
  have hdl : ∀ k < 4, ∀ o l, o + l ≤ 128 → Region.Disjoint ⟨at' S (Layout.laneA k + o), l⟩ ⟨AU, p.n⟩ := by
    intro k hk o l hl
    exact (hd.sub_right (Offset.sub_base S (by rw [laneA_eq, show Layout.oSigTmp = 31648 from rfl]; omega_using [hk, hl]))).symm
  simp only [List.cons_append, List.nil_append]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (hin 1 (by decide)) fun t₁ u₁ => ?_
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 2))
    (by rw [var, Proof.Sha3.X86_64.ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.rd, u₁.wr]; exact hin 2 (by decide)) fun t₂ u₂ => ?_
  refine wp_addm (a := at' S (Layout.oVar 2 3))
    (by rw [var, Proof.Sha3.X86_64.ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 3 (by decide)) fun t₃ u₃ => ?_
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hg₃ : ∀ g, g ≠ .rsi → g ≠ .rdx → t₃.gpr g = t.gpr g := fun g h h' => by
    rw [u₃.other _ h', u₂.other _ h', u₁.other _ h]
  have hdx : t₃.gpr .rdx = BitVec.ofNat 64 (U2 + J) := by
    rw [u₃.gpr, u₂.gpr, u₂.mem, u₁.mem, h2, h3, BitVec.ofNat_add_ofNat]
  have hsi : t₃.gpr .rsi = AU := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h1]
  -- the captures
  let P : Nat → State → Prop := fun c u =>
    (∀ g, g ≠ .rax → g ≠ .rdi → u.gpr g = t₃.gpr g) ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
    (∀ j < p.n, u.mem (AU + BitVec.ofNat 64 j) =
      if U2 + J ≤ idx ∧ idx < U2 + J + c then
        t.mem (at' S (Layout.laneA (idx - (U2 + J)) + p.n + 32 + j)) ^^^ t.mem (AU + BitVec.ofNat 64 j)
      else t.mem (AU + BitVec.ofNat 64 j)) ∧
    Frame [⟨AU, p.n⟩] t.mem u.mem
  have hP := wp_flatMap (P := P) 4 (s := t₃) ⟨fun _ _ _ => rfl, by rw [u₃.rd, u₂.rd, u₁.rd],
      by rw [u₃.wr, u₂.wr, u₁.wr], fun j _ => by rw [ite_eq_right (by omega_using []), hm₃], hm₃ ▸ Frame.refl _ _⟩
    fun c hc u ⟨g, r, w, sk, fr⟩ => by
      refine WP.mono (capture_ok (S := S) (au := AU) (C := U2 + J) hn hc (by rw [g _ (by decide) (by decide), hg₃ _ (by decide) (by decide), hbx])
        (by rw [g _ (by decide) (by decide), hdx]) (by rw [g _ (by decide) (by decide), hg₃ _ (by decide) (by decide), h13])
        (by rw [g _ (by decide) (by decide), hsi]) (by omega_using [hC]) hidx (by rw [w]; exact hw)
        (fun w' hw' => by rw [w]; exact hout w' hw')
        (by rw [show Layout.laneA c + p.n + 32 = Layout.laneA c + (p.n + 32) by omega_using []]
            exact hdl c hc _ _ (by omega_using [hn32]))) fun u' ⟨g', r', w', c', f'⟩ => ?_
      refine ⟨fun g'' h1 h2 => by rw [g' _ h1 h2, g _ h1 h2], by rw [r', r], by rw [w', w], fun j hj => ?_,
        fr.trans f'⟩
      have hlane : u.mem (at' S (Layout.laneA c + p.n + 32 + j)) = t.mem (at' S (Layout.laneA c + p.n + 32 + j)) := by
        refine keepS fr fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        rw [show Layout.laneA c + p.n + 32 + j = Layout.laneA c + (p.n + 32 + j) by omega_using []]
        exact hdl c hc _ _ (by omega_using [hn32, hj])
      rw [c' j hj, sk j hj, hlane]
      by_cases e : U2 + J + c = idx
      · rw [ite_eq_left e, ite_eq_right (by omega_using [e]), ite_eq_left (by omega_using [e, hc]),
          show idx - (U2 + J) = c by omega_using [e]]
      · rw [ite_eq_right e, zero_xor8]
        by_cases e' : U2 + J ≤ idx ∧ idx < U2 + J + c
        · rw [ite_eq_left e', ite_eq_left (by omega_using [e'])]
        · rw [ite_eq_right e', ite_eq_right (by omega_using [e', e])]
  refine WP.block_append (WP.mono hP fun u ⟨g, r, w, sk, fr⟩ => ?_)
  -- the types
  let Q : Nat → State → Prop := fun c v =>
    (∀ g, g ≠ .rax → v.gpr g = u.gpr g) ∧ v.rd = t.rd ∧ v.wr = t.wr ∧
    (∀ k < c, bytesAt v.mem (at' S (Layout.laneA k + p.n + 16)) 4 = toByte 3 4) ∧ Frame (typeRs p.n S) u.mem v.mem
  refine WP.mono (wp_flatMap (P := Q) 4 (s := u) ⟨fun _ _ => rfl, r, w, fun _ h => absurd h (by omega_using []),
      Frame.refl _ _⟩ fun c hc v ⟨g', r', w', ty, fr'⟩ => ?_) fun t' ⟨g', r', w', ty, fr'⟩ => ?_
  · have hla := laneA_eq c
    have hL := Nat.mul_le_mul_left 128 (show c ≤ 3 by omega_using [hc])
    refine setField_ok (by decide) (by decide : 3 < 2 ^ 31) (by
        rw [g' _ (by decide), g _ (by decide) (by decide), hg₃ _ (by decide) (by decide), hbx]
        simp only [Layout.adrsOff]; exact Levels.in_scr (by rw [w']; exact hw) (by omega_using [hla, hL, hn32]))
      fun v' f => WP.block_nil ?_
    have hbv : v.gpr .rbx = S := by rw [g' _ (by decide), g _ (by decide) (by decide), hg₃ _ (by decide) (by decide), hbx]
    simp only [hbv, Layout.adrsOff] at f
    refine ⟨fun g'' h => by rw [f.gpr _ h, g' _ h], by rw [f.rd, r'], by rw [f.wr, w'], fun k hk => ?_,
      fr'.trans (f.frame.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)⟩
    by_cases e : k = c
    · subst e; exact f.bytes
    · rw [show Layout.laneA k + p.n + 16 = Layout.laneA k + (p.n + 16) by omega_using [],
        keepSB f.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [show Layout.laneA c + p.n + 16 = Layout.laneA c + (p.n + 16) by omega_using []]
          exact lane_disj (by omega_using [hk, hc]) hc e (by omega_using [hn32]) (by omega_using [hn32]) S) (by decide),
        ← show Layout.laneA k + p.n + 16 = Layout.laneA k + (p.n + 16) by omega_using []]
      exact ty k (by omega_using [hk, e])
  · refine ⟨fun g'' h1 h2 h3 h4 => by rw [g' _ h1, g _ h1 h2, hg₃ _ h3 h4], r', w', fun j hj => ?_, ty, ?_⟩
    · rw [← sk j hj]
      refine fr' _ fun r hr => ?_
      simp only [typeRs, List.mem_map, List.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      have := (hdl k hk (p.n + 16) 4 (by omega_using [hn32])).symm
      rw [show Layout.laneA k + (p.n + 16) = Layout.laneA k + p.n + 16 by omega_using []] at this
      exact fun hc => this (AU + BitVec.ofNat 64 j) (by
        simp only [Region.Contains]
        rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj, hn32])]
        omega_using [hj]) hc
    · intro x hx
      rw [fr' x fun r hr => hx r (List.mem_cons_of_mem _ hr), fr x fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hx _ (List.mem_cons_self ..)]

/-! ## The leaves to the nodes -/

/-- What the last block of `leafBody` does: the four outputs to the nodes `J`
to `J + 3`, `J + 4` to variable 3, compared with `P`. -/
structure OutP (n : Nat) (S : Addr) (t t' : State) (J P : Nat) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  out : ∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (J + k) * n)) n = bytesAt t.mem (at' S (Layout.laneA k + n + 32)) n
  v3 : t'.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 (J + 4)
  cf : t'.cf = some (decide (J + 4 < P))
  frame : Frame [⟨at' S (Layout.oN + J * n), 4 * n⟩, ⟨at' S (Layout.oVar 2 3), 8⟩] t.mem t'.mem

theorem out_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {J P : Nat} {t : State}
    (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (h3 : t.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 J)
    (hJ : (J + 4) * p.n ≤ 32 * Layout.nodeSlots) (hP : P < 2 ^ 31) :
    WP isa (.block (([.mov .rdx (.mem (var 3))] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN (⟨p.n, p.len⟩ : Layout).n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        (List.range 4).flatMap (fun k => copyWords .rdx (Layout.oN + (⟨p.n, p.len⟩ : Layout).n * k) .rbx
          (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) ((⟨p.n, p.len⟩ : Layout).n / 8)) ++
        ([.mov .rax (.mem (var 3)), .alu .add .rax (.imm 4), .store (var 3) .rax,
          .alu .cmp .rax (.imm (BitVec.ofNat 32 P))] : List Instr))) t
      fun t' => OutP p.n S t t' J P := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have eN : Layout.oN = 12640 := rfl
  have eNS : Layout.nodeSlots = 520 := rfl
  have hv3 : Layout.oVar 2 3 = 2728 := rfl
  have hJ4 : (J + 4) * p.n = J * p.n + 4 * p.n := Nat.add_mul _ _ _
  have hJn : J < 2 ^ 16 := by
    have : J + 4 ≤ (J + 4) * p.n := Nat.le_mul_of_pos_right _ (by omega_using [hn]); omega_using [this, hJ, eNS]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 3)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (Levels.in_scr' hw (by rw [hv3]; omega_using [])) fun t₁ u₁ => ?_
  refine Levels.mulN_ok hn (by decide) fun t₂ h₂ g₂ m₂ r₂ w₂ => ?_
  refine Levels.wp_add fun t₃ u₃ => ?_
  have hdx : t₃.gpr .rdx = at' S (J * p.n) := by
    rw [u₃.gpr, h₂, u₁.gpr, g₂ _ (by decide) (by decide), u₁.other _ (by decide), hbx, h3, BitVec.ofNat_mul_ofNat,
      BitVec.add_comm]
  have hg₃ : ∀ g, g ≠ .rdx → g ≠ .rcx → t₃.gpr g = t.gpr g := fun g h h' => by
    rw [u₃.other _ h, g₂ _ h h', u₁.other _ h]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, m₂, u₁.mem]
  have hb₃ : t₃.gpr .rbx = S := by rw [hg₃ _ (by decide) (by decide), hbx]
  let P' : Nat → State → Prop := fun c u =>
    (∀ g, g ≠ .rax → u.gpr g = t₃.gpr g) ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
    (∀ k < c, bytesAt u.mem (at' S (Layout.oN + (J + k) * p.n)) p.n =
      bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n) ∧
    Frame [⟨at' S (Layout.oN + J * p.n), 4 * p.n⟩] t.mem u.mem
  refine WP.block_append (WP.mono (wp_flatMap (P := P') 4 (s := t₃) ⟨fun _ _ => rfl, by rw [u₃.rd, r₂, u₁.rd],
      by rw [u₃.wr, w₂, u₁.wr], fun _ h => absurd h (by omega_using []), hm₃ ▸ Frame.refl _ _⟩
    fun c hc u ⟨g, r, w, o, fr⟩ => ?_) fun u ⟨g, r, w, o, fr⟩ => ?_)
  · have hla := laneA_eq c
    have hL := Nat.mul_le_mul_left 128 (show c ≤ 3 by omega_using [hc])
    have hcn : (J + c) * p.n + p.n ≤ (J + 4) * p.n := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hc])
    have hcn' : (J + c) * p.n = J * p.n + p.n * c := by rw [Nat.add_mul, Nat.mul_comm c]
    refine WP.mono (Levels.copy_ok (S := S) (a := J * p.n) (b := 0) (d₁ := Layout.laneA c + p.n + 32)
      (d₂ := Layout.oN + p.n * c) (by decide) (by decide) (p.n / 8) u
      (by rw [g _ (by decide), hdx]) (by rw [g _ (by decide), hb₃]; exact Levels.scr0 S) (by rw [w]; exact hw)
      (by omega_using [e8, hla, hL, hn32]) (by omega_using [e8, eN, hJ, eNS, hJ4, hcn, hcn'])
      (by omega_using [e8, eN, hla, hL, hn32, hcn'])) fun u' ⟨g', r', w', c', f'⟩ => ?_
    rw [e8] at c' f'
    have hlane : ∀ k < 4, ∀ i < p.n, u.mem (at' S (Layout.laneA k + p.n + 32 + i)) =
        t.mem (at' S (Layout.laneA k + p.n + 32 + i)) := fun k hk i hi => keepS fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (.inl (by rw [laneA_eq]; omega_using [hk, hi, hn32, eN])) (by rw [laneA_eq]; omega_using [hk, hi, hn32])
        (by omega_using [eN, hJ, eNS, hJ4])
    refine ⟨fun g'' h => by rw [g' _ h, g _ h], by rw [r', r], by rw [w', w], fun k hk => ?_, ?_⟩
    · by_cases e : k = c
      · subst e
        refine bytesAt_ext fun i hi => ?_
        rw [Levels.add_add, Levels.add_add, show Layout.oN + (J + k) * p.n + i = J * p.n + (Layout.oN + p.n * k) + i by
          omega_using [hcn'], c' i hi, show 0 + (Layout.laneA k + p.n + 32) + i = Layout.laneA k + p.n + 32 + i by
          omega_using [], hlane k hc i hi]
      · have hkn : (J + k) * p.n + p.n ≤ (J + 4) * p.n := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hk, hc])
        have hkn' : (J + k) * p.n = J * p.n + p.n * k := by rw [Nat.add_mul, Nat.mul_comm k]
        rw [keepSB f' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            rw [show J * p.n + (Layout.oN + p.n * c) = Layout.oN + (J + c) * p.n by omega_using [hcn']]
            rcases Nat.lt_or_gt_of_ne e with h | h
            · have : (J + k) * p.n + p.n ≤ (J + c) * p.n := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [h])
              exact dS S (.inl (by omega_using [this])) (by omega_using [eN, hJ, eNS, hJ4, hkn])
                (by omega_using [eN, hJ, eNS, hJ4, hcn])
            · have : (J + c) * p.n + p.n ≤ (J + k) * p.n := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [h])
              exact dS S (.inr (by omega_using [this])) (by omega_using [eN, hJ, eNS, hJ4, hkn])
                (by omega_using [eN, hJ, eNS, hJ4, hcn])) (by omega_using [hn32])]
        exact o k (by omega_using [hk, e])
    · refine fr.trans (f'.sub fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega_using [eN]) (by omega_using [hcn, hcn', hJ4])⟩
  -- the next leaf
  have hb : u.gpr .rbx = S := by rw [g _ (by decide), hb₃]
  have hw' : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [w]; exact hw
  have hv : u.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 J := by
    rw [← h3]
    exact keepSW fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (.inl (by rw [hv3]; omega_using [eN])) (by rw [hv3]; omega_using []) (by omega_using [eN, hJ, eNS, hJ4])
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 3)) (by rw [var, Proof.Sha3.X86_64.ea_at, hb])
    (Levels.in_scr' hw' (by rw [hv3]; omega_using [])) fun v₁ e₁ => ?_
  refine Proof.Sha3.X86_64.wp_addi fun v₂ e₂ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 2 3))
    (by rw [var, Proof.Sha3.X86_64.ea_at, e₂.other _ (by decide), e₁.other _ (by decide), hb])
    (by rw [e₂.wr, e₁.wr]; exact Levels.in_scr hw' (by rw [hv3]; omega_using [])) fun v₃ g₃ m₃ r₃ w₃ => ?_
  refine wp_cmpiC fun t' g' m' r' w' _ cf' => WP.block_nil ?_
  have hax : v₂.gpr .rax = BitVec.ofNat 64 (J + 4) := by
    rw [e₂.gpr, e₁.gpr, hv, show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 by decide,
      BitVec.ofNat_add_ofNat]
  refine ⟨fun g'' h1 h2 h3 => ?_, by rw [r', r₃, e₂.rd, e₁.rd, r], by rw [w', w₃, e₂.wr, e₁.wr, w], fun k hk => ?_, ?_,
    ?_, ?_⟩
  · rw [g', g₃, e₂.other _ h1, e₁.other _ h1, g _ h1, hg₃ _ h3 h2]
  · rw [m', m₃, e₂.mem, e₁.mem, ← o k hk]
    refine keepSB ((Frame.refl [⟨at' S (Layout.oVar 2 3), 8⟩] _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (fun r hr => ?_) (by omega_using [hn32])
    · simp only [List.mem_singleton] at hr; subst hr
      have hkn : (J + k) * p.n + p.n ≤ (J + 4) * p.n := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hk])
      exact dS S (.inr (by rw [hv3]; omega_using [eN])) (by omega_using [eN, hJ, eNS, hJ4, hkn]) (by rw [hv3]; omega_using [])
  · rw [m', m₃, Mem.readW_writeW_self64, hax]
  · rw [cf', g₃, hax, Levels.sx_ofNat hP, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hJn]), Nat.mod_eq_of_lt (by omega_using [hP])]
  · rw [m', m₃, e₂.mem, e₁.mem]
    have hrs : ∀ r ∈ [(⟨at' S (Layout.oN + J * p.n), 4 * p.n⟩ : Region)],
        r ∈ [(⟨at' S (Layout.oN + J * p.n), 4 * p.n⟩ : Region), ⟨at' S (Layout.oVar 2 3), 8⟩] := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    exact (fr.mono hrs).writeW (r := ⟨at' S (Layout.oVar 2 3), 8⟩) (by simp) _ (Region.contains_self _ _)

/-! ## What the code leaves of `scratch` -/

/-- The bytes of `Env`: the round constants, and each lane's `PK.seed` and `a16`. -/
def EnvB (n q : Nat) : Prop :=
  (1600 ≤ q ∧ q < 2368) ∨ (3296 ≤ q ∧ q < 3808 ∧ (q - 3296) % 128 < n + 16) ∨
    (3808 ≤ q ∧ q < 12640 ∧ (q - 3808) % 2208 < n + 16)

/-- `Env` in a memory that agrees on its bytes. -/
theorem env_bytes {p : Params} (hn32 : p.n ≤ 32) {m m' : Mem} {S : Addr} {pk a : List Byte} (hE : Env p m S pk a)
    (h : ∀ q, EnvB p.n q → m' (at' S q) = m (at' S q)) : Env p m' S pk a := by
  have hb : ∀ o l, (∀ i < l, EnvB p.n (o + i)) → bytesAt m' (at' S o) l = bytesAt m (at' S o) l := fun o l hl =>
    bytesAt_ext fun i hi => by rw [Levels.add_add]; exact h _ (hl i hi)
  refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [← hE.rc r hr k hk]
    exact Mem.readW_congr fun i hi => by
      rw [Levels.add_add]
      exact h _ (.inl (by omega_using [hr, hk, hi]))
  · rw [hb _ _ fun i hi => .inr (.inl (by rw [laneA_eq]; omega_using [hk, hi, hn32]))]; exact hE.seedA k hk
  · rw [hb _ _ fun i hi => .inr (.inr (by
      rw [show Layout.laneB k = 3808 + 2208 * k from rfl]; omega_using [hk, hi, hn32]))]; exact hE.seedB k hk
  · rw [hb _ _ fun i hi => .inr (.inl (by rw [laneA_eq]; omega_using [hk, hi, hn32]))]; exact hE.adrsA k hk
  · rw [hb _ _ fun i hi => .inr (.inr (by
      rw [show Layout.laneB k = 3808 + 2208 * k from rfl]; omega_using [hk, hi, hn32]))]; exact hE.adrsB k hk

/-- `SK.seed` in a memory that agrees on its bytes. -/
theorem sk_bytes {p : Params} {m m' : Mem} {S : Addr} {sk : List Byte} (hs : SkAt p m S sk)
    (h : ∀ q, 3168 ≤ q → q < 3168 + p.n → m' (at' S q) = m (at' S q)) : SkAt p m' S sk := by
  unfold SkAt at hs ⊢
  rw [← hs]
  exact bytesAt_ext fun i hi => by
    rw [Levels.add_add, show Layout.oSkSeed = 3168 from rfl]
    exact h _ (by omega_using []) (by omega_using [hi])

/-- A byte below `oSigTmp` outside a region of `scratch`, of a region outside it below `oSigTmp`. -/
theorem dq (S : Addr) {q o l : Nat} (hq : q < 31648) (h : q < o ∨ o + l ≤ q) (hl : o + l ≤ 2 ^ 16) :
    Region.Disjoint ⟨at' S q, 1⟩ ⟨at' S o, l⟩ :=
  dS S (by omega_using [h]) (by omega_using [hq]) hl

theorem dqlow {S : Addr} {X : Region} (h : X.Disjoint ⟨S, Layout.oSigTmp⟩) {q : Nat} (hq : q < 31648) :
    Region.Disjoint ⟨at' S q, 1⟩ X :=
  (h.sub_right (Offset.sub_base S (by rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hq]))).symm

/-- What four leaves leave. -/
abbrev leafW (n : Nat) (S AU : Addr) (J : Nat) (sp : Addr) (stack : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (Layout.oVar 2 3), 8⟩, ⟨at' S (Layout.oN + J * n), 4 * n⟩, ⟨AU, n⟩,
    below sp stack] ++ laneRs n S

/-- A part of `scratch` below `oSigTmp` outside such a list of regions. -/
theorem dW {n : Nat} (hn32 : n ≤ 32) {S AU sp : Addr} {stack A B C D o l : Nat}
    (hAU : Region.Disjoint ⟨AU, n⟩ ⟨S, Layout.oSigTmp⟩) (hst : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩)
    (hl : o + l ≤ 31648) (h₀ : 1600 ≤ o) (h₁ : o + l ≤ 2368 ∨ 2400 ≤ o) (h₂ : o + l ≤ A ∨ A + B ≤ o)
    (h₃ : o + l ≤ C ∨ C + D ≤ o) (hB : A + B ≤ 2 ^ 16) (hD : C + D ≤ 2 ^ 16)
    (h₄ : ∀ k < 4, o + l ≤ Layout.laneA k + n + 16 ∨ Layout.laneA k + n + 32 + n ≤ o) :
    ∀ r ∈ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S A, B⟩, ⟨at' S C, D⟩, ⟨AU, n⟩, below sp stack] ++ laneRs n S,
      Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, laneRs, List.mem_map, List.mem_range] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
  · exact Offset.disjoint_base S h₀ (by omega_using [hl])
  · exact dS S (by omega_using [h₁]) (by omega_using [hl]) (by decide)
  · exact dS S h₂ (by omega_using [hl]) hB
  · exact dS S h₃ (by omega_using [hl]) hD
  · exact (hAU.sub_right (Offset.sub_base S (by rw [show Layout.oSigTmp = 31648 from rfl]; exact hl))).symm
  · exact (hst.sub_right (Levels.sub_scr S (by omega_using [hl]))).symm
  · exact dS S (by have := h₄ k hk; omega_using [this]) (by omega_using [hl])
      (by rw [laneA_eq]; omega_using [hk, hn32])

/-- What `leafBody` does: four leaves `V4 + U2 + J` to that plus 3 (`V4` the
first of the tree, `U2` of the subtree, `J` in it), their nodes; the private
key value of the tree's index `idx` XORed into the signature at `AU` if it is
one of them; the next leaf `J + 4`, compared with `P`. -/
structure LeafP (p : Params) (S AU : Addr) (stack : Nat) (pkSeed a16 skSeed : List Byte) (kp V4 U2 J idx P : Nat)
    (t t' : State) : Prop where
  cs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  mx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10
  v3 : t'.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 (J + 4)
  cf : t'.cf = some (decide (J + 4 < P))
  nodes : ∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (J + k) * p.n)) p.n =
    F p pkSeed (fld a16 3 kp 0 (V4 + U2 + J + k)) (prf p pkSeed skSeed (fld a16 6 kp 0 (V4 + U2 + J + k)))
  sk : ∀ j < p.n, t'.mem (AU + BitVec.ofNat 64 j) =
    if U2 + J ≤ idx ∧ idx < U2 + J + 4 then
      (prf p pkSeed skSeed (fld a16 6 kp 0 (V4 + idx))).getD j 0 ^^^ t.mem (AU + BitVec.ofNat 64 j)
    else t.mem (AU + BitVec.ofNat 64 j)
  frame : Frame (leafW p.n S AU J (t.gpr .rsp) stack) t.mem t'.mem

theorem mulN_nm (n : Nat) (r t : Reg) :
    (Impl.SlhDsa.X86_64.Wots.mulN n r t).all (fun i => !loadsMxcsr i) = true := by
  unfold Impl.SlhDsa.X86_64.Wots.mulN; split <;> rfl

theorem copyWords_nm (t : Reg) (d₂ : Nat) (s : Reg) (d₁ w : Nat) :
    (copyWords t d₂ s d₁ w).all (fun i => !loadsMxcsr i) = true := by
  simp [copyWords, List.all_flatMap, loadsMxcsr]

theorem nmA (L : Layout) : (([.mov .r10 (.mem (var 4)), .alu .add .r10 (.mem (var 2)), .alu .add .r10 (.mem (var 3))] : List Instr) ++
    (List.range 4).flatMap (fun k => leafAdrs L 6 k ++
      copyWords .rbx (Layout.laneA k + L.msgOff) .rbx Layout.oSkSeed (L.n / 8)) : List Instr).all
    (fun i => !loadsMxcsr i) = true := by
  simp only [leafAdrs, List.all_append, List.all_flatMap, copyWords_nm, setField, setFieldR]
  simp [loadsMxcsr]

theorem nmB (L : Layout) : (([.mov .rsi (.mem (var 1)), .mov .rdx (.mem (var 2)), .alu .add .rdx (.mem (var 3))] : List Instr) ++
    (List.range 4).flatMap (captureSk L) ++
    (List.range 4).flatMap (fun k => setField .rbx (Layout.laneA k + L.adrsOff + 16) 3) : List Instr).all
    (fun i => !loadsMxcsr i) = true := by
  simp only [captureSk, List.all_append, List.all_flatMap, setField]
  simp [loadsMxcsr]

theorem nmC (L : Layout) (P : Nat) : (([.mov .rdx (.mem (var 3))] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN L.n .rdx .rcx ++
    ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
    (List.range 4).flatMap (fun k => copyWords .rdx (Layout.oN + L.n * k) .rbx (Layout.laneA k + L.msgOff) (L.n / 8)) ++
    ([.mov .rax (.mem (var 3)), .alu .add .rax (.imm 4), .store (var 3) .rax,
      .alu .cmp .rax (.imm (BitVec.ofNat 32 P))] : List Instr) : List Instr).all (fun i => !loadsMxcsr i) = true := by
  simp only [List.all_append, List.all_flatMap, copyWords_nm, mulN_nm]
  simp [loadsMxcsr]

/-! ## Four leaves -/

theorem prf_shake {p : Params} (hf : p.family = .shake) (pk sk : List Byte) (a : Adrs) :
    prf p pk sk a = Spec.Sha3.shake256 (pk ++ a ++ sk) p.n := by
  simp only [prf, hf, shakeAdrs]

theorem F_shake {p : Params} (hf : p.family = .shake) (pk : List Byte) (a : Adrs) (M : List Byte) :
    F p pk a M = Spec.Sha3.shake256 (pk ++ a ++ M) p.n := by
  simp only [F, hf, shakeAdrs]

/-- A lane of `A`: `PK.seed ‖ a16 ‖` its fields `‖` its message. -/
theorem lane_bytes {p : Params} {m : Mem} {S : Addr} {pk a16 F16 M : List Byte} {k L : Nat}
    (hE : Env p m S pk a16) (hk : k < 4) (hf : bytesAt m (at' S (Layout.laneA k + p.n + 16)) 16 = F16)
    (hm : bytesAt m (at' S (Layout.laneA k + p.n + 32)) L = M) :
    bytesAt m (at' S (Layout.laneA k)) (p.n + 32 + L) = pk ++ (a16 ++ F16) ++ M := by
  rw [show p.n + 32 + L = p.n + (16 + (16 + L)) by omega_using [], bytesAt_split, bytesAt_split, bytesAt_split,
    show Layout.laneA k + p.n + 16 + 16 = Layout.laneA k + p.n + 32 by omega_using [], hE.seedA k hk, hE.adrsA k hk,
    hf, hm, List.append_assoc, List.append_assoc]

/-- The bytes of `16` from their first 4 and last 12. -/
theorem bytes16 (m : Mem) (S : Addr) (o : Nat) :
    bytesAt m (at' S o) 16 = bytesAt m (at' S o) 4 ++ bytesAt m (at' S (o + 4)) 12 := bytesAt_split m S o 4 12

theorem leaf_ok {p : Params} (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 8 ≤ stack) (hs63 : stack < 2 ^ 63) {S AU : Addr}
    {KP : BitVec 64} {V4 U2 J idx : Nat} {pkSeed a16 skSeed : List Byte} {t : State}
    (hbx : t.gpr .rbx = S) (h12 : t.gpr .r12 = KP) (hKP : KP.toNat < 2 ^ 32)
    (h13 : t.gpr .r13 = BitVec.ofNat 64 idx) (hidx : idx < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩)
    (hE : Env p t.mem S pkSeed a16) (hsk : SkAt p t.mem S skSeed)
    (h1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (h2 : t.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2)
    (h3 : t.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 J)
    (h4 : t.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4)
    (hX : V4 + U2 + J + 4 < 2 ^ 32) (hJ : (J + 4) * p.n ≤ 32 * Layout.nodeSlots)
    (hout : ∀ w < p.n / 8, InRegions t.wr (AU + BitVec.ofNat 64 (8 * w)) 8)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) (hAs : Region.Disjoint ⟨AU, p.n⟩ (below (t.gpr .rsp) stack)) :
    WP isa (leafBody ⟨p.n, p.len⟩ p.a name T.code) t
      (LeafP p S AU stack pkSeed a16 skSeed KP.toNat V4 U2 J idx (2 ^ s p.a) t) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have hP : 2 ^ s p.a < 2 ^ 31 := Nat.pow_lt_pow_right (by decide) (by omega_using [hs9])
  have hv : ∀ i, Layout.oVar 2 i = 2704 + 8 * i := fun _ => rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have eN : Layout.oN = 12640 := rfl
  have eNS : Layout.nodeSlots = 520 := rfl
  -- bytes of `scratch` below the lanes `B`, outside the lanes' fields and messages
  have dRs : ∀ q, q < 31648 → (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 32 + p.n ≤ q) →
      ∀ r ∈ laneRs p.n S, Region.Disjoint ⟨at' S q, 1⟩ r := fun q hq h r hr => by
    simp only [laneRs, List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    exact dq S hq (by have := h k hk; omega_using [this]) (by rw [laneA_eq]; omega_using [hk, hn32])
  have dTy : ∀ q, q < 31648 → (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 20 ≤ q) →
      ∀ r ∈ typeRs p.n S, Region.Disjoint ⟨at' S q, 1⟩ r := fun q hq h r hr => by
    simp only [typeRs, List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    exact dq S hq (by have := h k hk; omega_using [this]) (by rw [laneA_eq]; omega_using [hk, hn32])
  -- the regions of a call of `thash4` on the lanes `A`
  have dT4 : ∀ (sp : Addr) (q : Nat), q < 31648 → (below sp stack).Disjoint ⟨S, 2 ^ 16⟩ →
      1600 ≤ q ∧ (q < 2368 ∨ 2400 ≤ q) →
      (∀ k < 4, q < Layout.laneA k + p.n + 32 ∨ Layout.laneA k + p.n + 32 + p.n ≤ q) →
      ∀ r ∈ (List.range 4).map (fun k => (⟨at' S (laneAt Layout.oA Layout.strideA k + p.n + 32), p.n⟩ : Region)) ++
        [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below sp stack], Region.Disjoint ⟨at' S q, 1⟩ r := by
    intro sp q hq hsp h2400 h r hr
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
    · have := h k hk
      rw [laneA_eq] at this
      exact dq S hq (by simp only [laneAt, Layout.oA, Layout.strideA]; omega_using [this]) (by
        simp only [laneAt, Layout.oA, Layout.strideA]; omega_using [hk, hn32])
    · exact Offset.disjoint_base S (by omega_using [h2400]) (by omega_using [hq])
    · exact dq S hq (by omega_using [h2400]) (by decide)
    · exact (hsp.sub_right (Levels.sub_scr S (by omega_using [hq]))).symm
  have ha16 : a16.length = 16 := by rw [← hE.adrsA 0 (by decide)]; simp [bytesAt]
  unfold leafBody
  -- the lanes for the private key values
  refine WP.seq (WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using nmA ⟨p.n, p.len⟩)
    (lanesA_ok hn hbx h12 hKP hw h4 h2 h3 (by omega_using [hX])) fun t₁ A mx₁ => ?_)
  have hb₁ : t₁.gpr .rbx = S := by rw [A.gpr _ (by decide) (by decide) (by decide), hbx]
  have hsp₁ : t₁.gpr .rsp = t.gpr .rsp := A.gpr _ (by decide) (by decide) (by decide)
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₁.wr := by rw [A.wr]; exact hw
  have kA : ∀ q, q < 31648 → (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 32 + p.n ≤ q) →
      t₁.mem (at' S q) = t.mem (at' S q) := fun q hq h => keepS A.frame (dRs q hq h)
  have hE₁ : Env p t₁.mem S pkSeed a16 := env_bytes hn32 hE fun q hq => kA q (by simp only [EnvB] at hq; omega_using [hq])
    fun k hk => by simp only [EnvB] at hq; rw [laneA_eq]; omega_using [hq, hk, hn32]
  -- the private key values
  refine WP.seq (WP.mono (t4g_ok T name hn hst hs63 (o := Layout.oA) (st := Layout.strideA) (len := 2 * p.n + 32)
    (.inl ⟨rfl, rfl⟩) (by omega_using []) (by omega_using [hn8]) (by simp only [Layout.strideA]; omega_using [hn32])
    hb₁ hw₁ hS (by rw [hsp₁]; exact hstk) hE₁.rc) fun t₂ C₁ => ?_)
  have hb₂ : t₂.gpr .rbx = S := by rw [C₁.cs _ (by simp [calleeSaved]), hb₁]
  have hsp₂ : t₂.gpr .rsp = t.gpr .rsp := by rw [C₁.cs _ (by simp [calleeSaved]), hsp₁]
  have hw₂ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₂.wr := by rw [C₁.wr]; exact hw₁
  have k₁ : ∀ q, q < 31648 → 1600 ≤ q ∧ (q < 2368 ∨ 2400 ≤ q) → (∀ k < 4, q < Layout.laneA k + p.n + 32 ∨ Layout.laneA k + p.n + 32 + p.n ≤ q) →
      t₂.mem (at' S q) = t₁.mem (at' S q) := fun q hq h₀ h =>
    keepS C₁.frame (dT4 _ q hq (by rw [hsp₁]; exact hstk) h₀ h)
  have hvar : ∀ i, i < 9 → ∀ u : State, (∀ q, 2704 ≤ q → q < 2776 → u.mem (at' S q) = t.mem (at' S q)) →
      u.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64 := fun i hi u h =>
    Mem.readW_congr fun j hj => by rw [Levels.add_add, hv]; exact h _ (by omega_using []) (by omega_using [hi, hj])
  have hv₂ : ∀ q, 2704 ≤ q → q < 2776 → t₂.mem (at' S q) = t.mem (at' S q) := fun q h₁ h₂ => by
    rw [k₁ q (by omega_using [h₂]) (by omega_using [h₁]) fun k hk => .inl (by rw [laneA_eq]; omega_using [h₂]),
      kA q (by omega_using [h₂]) fun k hk => .inl (by rw [laneA_eq]; omega_using [h₂])]
  have hA₂ : ∀ j < p.n, t₂.mem (AU + BitVec.ofNat 64 j) = t.mem (AU + BitVec.ofNat 64 j) := fun j hj => by
    have e₁ := C₁.frame.bytes (R := ⟨AU, p.n⟩) (fun r hr => by
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
      · exact hd.sub_right (Offset.sub_base S (by simp only [laneAt, Layout.oA, Layout.strideA]; omega_using [hk, hn32, eT]))
      · exact hd.sub_right (Region.sub_prefix (by omega_using [eT]))
      · exact hd.sub_right (Offset.sub_base S (by omega_using [eT]))
      · rw [hsp₁]; exact hAs) (show p.n ≤ 2 ^ 64 by omega_using [hn32]) hj
    have e₀ := A.frame.bytes (R := ⟨AU, p.n⟩) (fun r hr => by
      simp only [laneRs, List.mem_map, List.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      exact hd.sub_right (Offset.sub_base S (by rw [laneA_eq]; omega_using [hk, hn32, eT]))) (show p.n ≤ 2 ^ 64 by omega_using [hn32]) hj
    rw [e₁, e₀]
  -- the capture, and the lanes for the leaves
  refine WP.seq (WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using nmB ⟨p.n, p.len⟩)
    (capB_ok (U2 := U2) (J := J) hn hb₂ (by rw [C₁.cs _ (by simp [calleeSaved]), A.gpr _ (by decide) (by decide) (by decide), h13])
      hw₂ (by rw [hvar 1 (by decide) _ hv₂, h1]) (by rw [hvar 2 (by decide) _ hv₂, h2])
      (by rw [hvar 3 (by decide) _ hv₂, h3]) (by omega_using [hX]) hidx
      (fun w hw' => by rw [C₁.wr, A.wr]; exact hout w hw') hd) fun t₃ B mx₃ => ?_)
  have hb₃ : t₃.gpr .rbx = S := by rw [B.gpr _ (by decide) (by decide) (by decide) (by decide), hb₂]
  have hsp₃ : t₃.gpr .rsp = t.gpr .rsp := by rw [B.gpr _ (by decide) (by decide) (by decide) (by decide), hsp₂]
  have hw₃ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₃.wr := by rw [B.wr]; exact hw₂
  have kB : ∀ q, q < 31648 → (∀ k < 4, q < Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 20 ≤ q) →
      t₃.mem (at' S q) = t₂.mem (at' S q) := fun q hq h => keepS B.frame fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact dqlow hd hq
    · exact dTy q hq h r hr
  have hE₂ : Env p t₂.mem S pkSeed a16 := env_bytes hn32 hE₁ fun q hq => k₁ q
    (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq])
    fun k hk => by simp only [EnvB] at hq; rw [laneA_eq]; omega_using [hq, hk, hn32]
  have hE₃ : Env p t₃.mem S pkSeed a16 := env_bytes hn32 hE₂ fun q hq => kB q
    (by simp only [EnvB] at hq; omega_using [hq])
    fun k hk => by simp only [EnvB] at hq; rw [laneA_eq]; omega_using [hq, hk, hn32]
  -- the leaves
  refine WP.seq (WP.mono (t4g_ok T name hn hst hs63 (o := Layout.oA) (st := Layout.strideA) (len := 2 * p.n + 32)
    (.inl ⟨rfl, rfl⟩) (by omega_using []) (by omega_using [hn8]) (by simp only [Layout.strideA]; omega_using [hn32])
    hb₃ hw₃ hS (by rw [hsp₃]; exact hstk) hE₃.rc) fun t₄ C₂ => ?_)
  have hb₄ : t₄.gpr .rbx = S := by rw [C₂.cs _ (by simp [calleeSaved]), hb₃]
  have hw₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₄.wr := by rw [C₂.wr]; exact hw₃
  have k₂ : ∀ q, q < 31648 → 1600 ≤ q ∧ (q < 2368 ∨ 2400 ≤ q) →
      (∀ k < 4, q < Layout.laneA k + p.n + 32 ∨ Layout.laneA k + p.n + 32 + p.n ≤ q) →
      t₄.mem (at' S q) = t₃.mem (at' S q) := fun q hq h₀ h =>
    keepS C₂.frame (dT4 _ q hq (by rw [hsp₃]; exact hstk) h₀ h)
  have hv₄ : ∀ q, 2704 ≤ q → q < 2776 → t₄.mem (at' S q) = t.mem (at' S q) := fun q h₁ h₂ => by
    rw [k₂ q (by omega_using [h₂]) (by omega_using [h₁]) fun k hk => .inl (by rw [laneA_eq]; omega_using [h₂]),
      kB q (by omega_using [h₂]) (fun k hk => .inl (by rw [laneA_eq]; omega_using [h₂])), hv₂ q h₁ h₂]
  -- the leaves to the nodes
  refine WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using nmC ⟨p.n, p.len⟩ (2 ^ s p.a))
    (out_ok (J := J) (P := 2 ^ s p.a) hn hb₄ hw₄ (by rw [hvar 3 (by decide) _ hv₄, h3]) hJ hP) fun t₅ O mx₅ => ?_
  -- the messages of the lanes, and what the hashes give
  have hX4 : ∀ k < 4, V4 + U2 + J + k < 2 ^ 32 := fun k hk => by omega_using [hX, hk]
  have hm₁ : ∀ k < 4, bytesAt t₁.mem (at' S (Layout.laneA k)) (2 * p.n + 32) =
      pkSeed ++ fld a16 6 KP.toNat 0 (V4 + U2 + J + k) ++ skSeed := fun k hk => by
    rw [show 2 * p.n + 32 = p.n + 32 + p.n by omega_using [], lane_bytes hE₁ hk (A.fields k hk) (A.msg k hk)]
    rw [hsk]; rfl
  have ho₁ : ∀ k < 4, bytesAt t₂.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      prf p pkSeed skSeed (fld a16 6 KP.toNat 0 (V4 + U2 + J + k)) := fun k hk => by
    rw [prf_shake hf, ← hm₁ k hk]; exact C₁.out k hk
  have hf₃ : ∀ k < 4, bytesAt t₃.mem (at' S (Layout.laneA k + p.n + 16)) 16 =
      toByte 3 4 ++ (toByte KP.toNat 4 ++ (toByte 0 4 ++ toByte (V4 + U2 + J + k) 4)) := fun k hk => by
    have hl := Nat.mul_le_mul_left 128 (show k ≤ 3 by omega_using [hk])
    have e₁ := A.fields k hk
    rw [bytes16] at e₁ ⊢
    rw [B.ty k hk]
    congr 1
    have e₂ : bytesAt t₁.mem (at' S (Layout.laneA k + p.n + 16 + 4)) 12 =
        toByte KP.toNat 4 ++ (toByte 0 4 ++ toByte (V4 + U2 + J + k) 4) :=
      (List.append_inj e₁ (by simp [bytesAt, toByte])).2
    rw [← e₂]
    refine bytesAt_ext fun i hi => ?_
    rw [Levels.add_add, kB _ (by rw [laneA_eq]; omega_using [hk, hi, hn32]) fun k' hk' => by
        rw [laneA_eq, laneA_eq]; omega_using [hk, hk', hi, hn32],
      k₁ _ (by rw [laneA_eq]; omega_using [hk, hi, hn32]) (by rw [laneA_eq]; omega_using [hk, hi, hn32]) fun k' hk' => by
        rw [laneA_eq, laneA_eq]; omega_using [hk, hk', hi, hn32]]
  have hm₃ : ∀ k < 4, bytesAt t₃.mem (at' S (Layout.laneA k)) (2 * p.n + 32) =
      pkSeed ++ fld a16 3 KP.toNat 0 (V4 + U2 + J + k) ++
        prf p pkSeed skSeed (fld a16 6 KP.toNat 0 (V4 + U2 + J + k)) := fun k hk => by
    rw [show 2 * p.n + 32 = p.n + 32 + p.n by omega_using [], lane_bytes hE₃ hk (hf₃ k hk) (L := p.n)
      (M := prf p pkSeed skSeed (fld a16 6 KP.toNat 0 (V4 + U2 + J + k))) (by
        rw [← ho₁ k hk]
        refine bytesAt_ext fun i hi => ?_
        rw [Levels.add_add]
        exact kB _ (by rw [laneA_eq]; omega_using [hk, hi, hn32]) fun k' hk' => by
          rw [laneA_eq, laneA_eq]; omega_using [hk, hk', hi, hn32])]
    rfl
  have ho₂ : ∀ k < 4, bytesAt t₄.mem (at' S (Layout.laneA k + p.n + 32)) p.n =
      F p pkSeed (fld a16 3 KP.toNat 0 (V4 + U2 + J + k)) (prf p pkSeed skSeed (fld a16 6 KP.toNat 0 (V4 + U2 + J + k))) :=
    fun k hk => by rw [F_shake hf, ← hm₃ k hk]; exact C₂.out k hk
  -- the signature's bytes, through the calls and the last block
  have hA₅ : ∀ j < p.n, t₅.mem (AU + BitVec.ofNat 64 j) = t₃.mem (AU + BitVec.ofNat 64 j) := fun j hj => by
    have e₂ := O.frame.bytes (R := ⟨AU, p.n⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hJ4 : (J + 4) * p.n = J * p.n + 4 * p.n := Nat.add_mul _ _ _
        exact hd.sub_right (Offset.sub_base S (by omega_using [eN, hJ, eNS, eT, hJ4]))
      · exact hd.sub_right (Offset.sub_base S (by rw [hv]; omega_using [eT]))) (show p.n ≤ 2 ^ 64 by omega_using [hn32]) hj
    have e₁ := C₂.frame.bytes (R := ⟨AU, p.n⟩) (fun r hr => by
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
      · exact hd.sub_right (Offset.sub_base S (by simp only [laneAt, Layout.oA, Layout.strideA]; omega_using [hk, hn32, eT]))
      · exact hd.sub_right (Region.sub_prefix (by omega_using [eT]))
      · exact hd.sub_right (Offset.sub_base S (by omega_using [eT]))
      · rw [hsp₃]; exact hAs) (show p.n ≤ 2 ^ 64 by omega_using [hn32]) hj
    rw [e₂, e₁]
  refine ⟨fun r hr => ?_, by rw [O.rd, C₂.rd, B.rd, C₁.rd, A.rd], by rw [O.wr, C₂.wr, B.wr, C₁.wr, A.wr],
    by rw [mx₅, C₂.mx, mx₃, C₁.mx, mx₁], O.v3, O.cf, fun k hk => by rw [O.out k hk, ho₂ k hk], fun j hj => ?_, ?_⟩
  · have hne : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hne
    rw [O.gpr _ h₁ h₂ h₃, C₂.cs _ hr, B.gpr _ h₁ h₄ h₅ h₃, C₁.cs _ hr, A.gpr _ h₁ h₆ h₇]
  · rw [hA₅ j hj, B.sk j hj, hA₂ j hj]
    by_cases e : U2 + J ≤ idx ∧ idx < U2 + J + 4
    · rw [ite_eq_left e, ite_eq_left e, show at' S (Layout.laneA (idx - (U2 + J)) + p.n + 32 + j) =
        at' S (Layout.laneA (idx - (U2 + J)) + p.n + 32) + BitVec.ofNat 64 j from (Levels.add_add _ _ _).symm,
        ← bytesAt_getD t₂.mem (at' S (Layout.laneA (idx - (U2 + J)) + p.n + 32)) hj, ho₁ _ (by omega_using [e]),
        show V4 + U2 + J + (idx - (U2 + J)) = V4 + idx by omega_using [e]]
    · rw [ite_eq_right e, ite_eq_right e]
  · -- the frame
    have sub : ∀ rs : List Region, (∀ r ∈ rs, ∃ r' ∈ leafW p.n S AU J (t.gpr .rsp) stack, Region.Sub r r') →
        ∀ {m m' : Mem}, Frame rs m m' → Frame (leafW p.n S AU J (t.gpr .rsp) stack) m m' := fun rs h m m' f => f.sub h
    have inL : ∀ k < 4, ⟨at' S (Layout.laneA k + p.n + 16), 16 + p.n⟩ ∈ leafW p.n S AU J (t.gpr .rsp) stack := fun k hk =>
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    have fT : ∀ (sp : Addr), sp = t.gpr .rsp → ∀ r ∈ (List.range 4).map (fun k =>
        (⟨at' S (laneAt Layout.oA Layout.strideA k + p.n + 32), p.n⟩ : Region)) ++
        [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below sp stack], ∃ r' ∈ leafW p.n S AU J (t.gpr .rsp) stack, Region.Sub r r' := by
      intro sp hsp r hr
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
      · exact ⟨_, inL k hk, Offset.sub S (by simp only [laneAt]; rw [laneA_eq]; simp only [Layout.oA, Layout.strideA]; omega_using [])
          (by simp only [laneAt]; rw [laneA_eq]; simp only [Layout.oA, Layout.strideA]; omega_using [])⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp [hsp], fun _ h => h⟩
    refine (sub _ (fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩) A.frame).trans
      ((sub _ (fT _ hsp₁) C₁.frame).trans ((sub _ (fun r hr => ?_) B.frame).trans
        ((sub _ (fT _ hsp₃) C₂.frame).trans (sub _ (fun r hr => ?_) O.frame))))
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, by simp, fun _ h => h⟩
      · simp only [typeRs, List.mem_map, List.mem_range] at hr
        obtain ⟨k, hk, rfl⟩ := hr
        exact ⟨_, inL k hk, Offset.sub S (by omega_using []) (by omega_using [])⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.SlhDsa.X86_64.Fors
