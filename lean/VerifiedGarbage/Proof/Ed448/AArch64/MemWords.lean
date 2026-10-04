import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed448.AArch64.Chain

/-!
# Ed448 on AArch64: words stored and loaded relative to a register

A list of `str` (`strs`) or `ldr` (`ldrs`) at offsets from one base
register, proven once by induction on the list: the stores write the words
in turn (`wrs`), each of which a later read finds if the offsets are
separate (`word_wrs`), and the loads read them.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs writeW_outside word_writeW_sep
  word_writeW_self)

/-- `str x_r, [b, #d]` for each `(r, d)`. -/
def strs (b : Reg) (ps : List (Reg × Nat)) : List Instr := ps.map fun p => .str .x p.1 b p.2

/-- `ldr x_r, [b, #d]` for each `(r, d)`. -/
def ldrs (b : Reg) (ps : List (Reg × Nat)) : List Instr := ps.map fun p => .ldr .x p.1 b p.2

/-- The registers' values `g` written in turn at their offsets from `base`. -/
def wrs (m : Mem) (base : Addr) (g : Reg → BitVec 64) : List (Reg × Nat) → Mem
  | [] => m
  | p :: ps => wrs (m.writeW (off base p.2) (g p.1)) base g ps

theorem strs_ok {base : Addr} (b : Reg) : ∀ (ps : List (Reg × Nat)) (s : State), s.gpr b = base →
    (∀ p ∈ ps, p.2 % 8 = 0 ∧ p.2 < 32768 ∧ InRegions s.wr (off base p.2) 8) →
    WP isa (.block (strs b ps)) s fun t => t = { s with mem := wrs s.mem base s.gpr ps }
  | [], s, _, _ => WP.block_nil rfl
  | p :: ps, s, hb, hw => by
    obtain ⟨h8, hl, hr⟩ := hw p List.mem_cons_self
    rw [strs, List.map_cons, WP.block_cons_iff]
    refine ⟨_, exec_str_x ⟨h8, hl⟩ (by rw [hb]; exact hr), ?_⟩
    rw [hb]
    exact WP.mono (strs_ok b ps _ hb fun q hq => hw q (List.mem_cons_of_mem _ hq)) fun t ht => ht

/-- Two words at offsets `d` and `e` do not overlap. -/
def Sep8 (d e : Nat) : Prop := d + 8 ≤ e ∨ e + 8 ≤ d

instance (d e : Nat) : Decidable (Sep8 d e) := inferInstanceAs (Decidable (_ ∨ _))

theorem word_wrs_of_sep (m : Mem) (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)) {d : Nat}, (∀ p ∈ ps, Sep8 p.2 d ∧ p.2 + 8 ≤ 2 ^ 64) →
      d + 8 ≤ 2 ^ 64 → word (wrs m base g ps) base d = word m base d
  | [], _, _, _ => rfl
  | p :: ps, d, h, hd => by
    rw [wrs, word_wrs_of_sep _ base g ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) hd]
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    exact word_writeW_sep m base _ h1.symm h2 hd

theorem word_wrs (m : Mem) (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)), ps.Pairwise (fun p q => Sep8 p.2 q.2) →
      (∀ p ∈ ps, p.2 + 8 ≤ 2 ^ 64) → ∀ p ∈ ps, word (wrs m base g ps) base p.2 = g p.1
  | [], _, _, _, hp => nomatch hp
  | p :: ps, hs, hl, q, hq => by
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [wrs, word_wrs_of_sep _ base g ps (fun r hr => ⟨hs.1 r hr |>.symm, hl r
        (List.mem_cons_of_mem _ hr)⟩) (hl _ List.mem_cons_self)]
      exact word_writeW_self m base _ _
    · exact word_wrs _ base g ps hs.2 (fun r hr => hl r (List.mem_cons_of_mem _ hr)) q hq
where
  symm {a b : Nat} (h : Sep8 a b) : Sep8 b a := h.symm

theorem wrs_outside (m : Mem) (base : Addr) (g : Reg → BitVec 64) {o n : Nat} (hn : o + n < 2 ^ 64) :
    ∀ (ps : List (Reg × Nat)), (∀ p ∈ ps, o ≤ p.2 ∧ p.2 + 8 ≤ o + n) →
      Outside base o n m (wrs m base g ps)
  | [], _ => Outside.refl _ _ _ _
  | p :: ps, h => by
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    exact ((writeW_outside m base (g p.1) (by omega)).mono h1 (by omega)).trans
      (wrs_outside _ base g hn ps fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem wrs_frame {R : Region} {m : Mem} (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)) (m' : Mem), Frame [R] m m' →
      (∀ p ∈ ps, R.Contains (off base p.2) 8) → Frame [R] m (wrs m' base g ps)
  | [], _, h, _ => h
  | p :: ps, _, h, hc => wrs_frame base g ps _
      (h.writeW (List.mem_singleton_self _) _ (hc p List.mem_cons_self))
      fun q hq => hc q (List.mem_cons_of_mem _ hq)

theorem ldrs_ok {base : Addr} (b : Reg) : ∀ (ps : List (Reg × Nat)) (s : State), s.gpr b = base →
    (∀ p ∈ ps, p.2 % 8 = 0 ∧ p.2 < 32768 ∧ InRegions (s.rd ++ s.wr) (off base p.2) 8 ∧ p.1 ≠ b) →
    (ps.map (·.1)).Nodup →
    WP isa (.block (ldrs b ps)) s fun t =>
      (∀ p ∈ ps, t.gpr p.1 = word s.mem base p.2) ∧ Keeps (ps.map (·.1)) s t
  | [], s, _, _, _ => WP.block_nil ⟨(fun _ h => nomatch h), Keeps.refl _ _⟩
  | p :: ps, s, hb, hw, hnd => by
    obtain ⟨h8, hl, hr, hpb⟩ := hw p List.mem_cons_self
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [ldrs, List.map_cons, WP.block_cons_iff]
    refine ⟨_, exec_ldr_x ⟨h8, hl⟩ (by rw [hb]; exact hr), ?_⟩
    let s1 := s.write .x p.1 (s.mem.readW (s.gpr b + BitVec.ofNat 64 p.2) 64)
    have k1 : ∀ r, r ≠ p.1 → s1.gpr r = s.gpr r := fun r hr =>
      RegUpd.gpr_write_of_ne s .x _ hr
    refine WP.mono (ldrs_ok b ps s1 ((k1 b (Ne.symm hpb)).trans hb) (fun q hq => hw q
      (List.mem_cons_of_mem _ hq)) hnd.2) fun t ⟨ht, kt⟩ => ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [kt.gpr _ hnd.1, RegUpd.gpr_write_self, BitVec.setWidth_eq, hb]
      · exact ht q hq
    · refine ⟨fun r hr => ?_, kt.mem, kt.rd, kt.wr, kt.sp⟩
      rw [List.map_cons, List.mem_cons, not_or] at hr
      rw [kt.gpr r hr.2, k1 r hr.1]

end VG.Proof.Ed448.AArch64
