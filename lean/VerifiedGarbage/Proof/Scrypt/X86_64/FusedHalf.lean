import VerifiedGarbage.Proof.Scrypt.X86_64.FusedSetup
namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.MdStream.X86_64 (wp_movm wp_addi)
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)

structure Head (p src dst : Addr) (s₀ s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rax : s.gpr .rax = src
  rdi : s.gpr .rdi = dst
  keep : ∀ r, r ≠ .rax → r ≠ .rdi → s.gpr r = s₀.gpr r

theorem head_ok {p b e o count : Addr} {s : State} (hsi : s.gpr .rsi = p)
    (hm : Meta p b e o count s.mem) (hs : InRegions s.wr p 64) (offset : Nat)
    (hoff : offset = 0 ∨ offset = 64) (odd : Bool) :
    WP isa (.block (fusedHead offset odd)) s (Head p (b + BitVec.ofNat 64 offset) (if odd then o else e) s) := by
  unfold fusedHead
  refine wp_movm (a := bufAt p 16) (by rw [ea_at, hsi])
    (Memory.InRegions.right (access hs (by decide))) fun a ua =>
    wp_addi fun c uc => ?_
  have si : c.gpr .rsi = p := by rw [uc.other _ (by decide), ua.other _ (by decide), hsi]
  refine wp_movm (a := bufAt p (if odd then 32 else 24)) (by rw [ea_at, si])
    (by rw [uc.rd, ua.rd, uc.wr, ua.wr]; exact Memory.InRegions.right (access hs (by cases odd <;> decide)
      (by cases odd <;> decide))) fun t ut => WP.block_nil ?_
  have mm : c.mem = s.mem := uc.mem.trans ua.mem
  refine ⟨ut.mem.trans mm, ut.rd.trans (uc.rd.trans ua.rd), ut.wr.trans (uc.wr.trans ua.wr), ?_, ?_,
    fun r h1 h2 => by rw [ut.other _ h2, uc.other _ h1, ua.other _ h1]⟩
  · rw [ut.other _ (by decide), uc.gpr, ua.gpr, hm.input]
    rcases hoff with rfl | rfl <;> rfl
  · rw [ut.gpr, mm]
    cases odd
    · exact hm.even
    · exact hm.odd

theorem half_ok {p b e o count prev : Addr} {s : State} (h : Words p (memWords s.mem prev) s)
    (hm : Meta p b e o count s.mem) (offset : Nat) (hoff : offset = 0 ∨ offset = 64) (odd : Bool)
    (hi : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 offset) 64)
    (hb : InRegions s.wr (if odd then o else e) 64) (hs : InRegions s.wr p 64)
    (hd : (bR (if odd then o else e)).Disjoint (scR p))
    (hsd : (bR (b + BitVec.ofNat 64 offset)).Disjoint (bR (if odd then o else e)))
    (hss : (bR (b + BitVec.ofNat 64 offset)).Disjoint (scR p)) :
    WP isa (fusedHalf offset odd) s fun t =>
      Words p (memWords t.mem (if odd then o else e)) t ∧
      bytesAt t.mem (if odd then o else e) 64 = Spec.Scrypt.salsa
        (xorBytes (bytesAt s.mem prev 64) (bytesAt s.mem (b + BitVec.ofNat 64 offset) 64)) ∧
      Frame [bR (if odd then o else e), slotR p, tempR p] s.mem t.mem ∧
      Meta p b e o count t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rsp = s.gpr .rsp := by
  refine WP.seq (WP.mono (head_ok h.rsi hm hs offset hoff odd) fun a ha => ?_)
  have hw : Words p (memWords a.mem prev) a := by
    rw [ha.mem]
    exact ⟨fun k hk => (ha.keep _ (wreg_ne k hk).1 (wreg_ne k hk).2.2.1).trans (h.regs k hk),
      fun k hk h12 => ha.mem ▸ h.slots k hk h12, (ha.keep _ (by decide) (by decide)).trans h.rsi⟩
  refine WP.mono (core_widen hw (by rw [ha.rd, ha.wr]; exact hi)
    (by rw [ha.wr]; exact hb) (by rw [ha.wr]; exact hs) hd hsd hss ha.rdi ha.rax)
    fun t ⟨wt, ot, ft, rt, wrt, _, spt⟩ => ?_
  rw [ha.mem] at ot ft
  exact ⟨wt, ot, ft, hm.frame hd ft, rt.trans ha.rd, wrt.trans ha.wr,
    spt.trans (ha.keep _ (by decide) (by decide))⟩
end VG.Proof.Scrypt.X86_64.Retained
