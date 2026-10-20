module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntryCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchFinishCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoop
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSafety
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchStart

/-! # Complete native parameter generation has the specified public-tape leakage -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private def initialPoint (p : SearchPublic) : SearchPoint := ⟨p, 0, p.remaining⟩
private def finalPoint (p : SearchPublic) : SearchEndPoint := ⟨p, searchTail p 0 p.remaining⟩

private theorem entry_started (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block entry) s (SearchCTL (initialPoint p)) :=
  WP.mono (search_start h) fun _ ht => ⟨s, ht⟩

private theorem loop_done (v : RoundImpl) (p : SearchPublic) (s : State) (h : SearchCTL (initialPoint p) s) :
    WP isa (.loop (iteration (candidateCode v)) .e) s (SearchCTDone (finalPoint p)) := by
  obtain ⟨original, h⟩ := h
  have hi : SearchInvariant p original (searchTail p 0 p.remaining) (p.remaining + 1) s :=
    ⟨0, p.remaining, rfl, h, rfl⟩
  exact WP.mono (search_loop v hi) fun _ ht => ⟨original, ht⟩

theorem search_code_ct (v : RoundImpl) :
    RelCT isa (Two SearchInput) (searchCode v) (fun _ _ => True) := by
  unfold searchCode code
  change RelCT isa _ (.seq _ (.seq _ _)) _
  exact RelCT.seq (two_post search_entry_ct entry_started)
    (RelCT.seq (two_post (two_map initialPoint (fun _ _ h => h) (search_loop_ct v)) (loop_done v))
      (two_map finalPoint (fun _ _ h => h) search_finish_ct))

private theorem search_public_descriptor {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨⟨hsp, hbytes, r0, r1, r2, r3, r4, r5, a0, a1, a2⟩, ac, hw⟩ := h
  have hrand := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hbytes
  have hc : candidateOfState s = candidateOfState t := by
    simp only [candidateOfState, r0, r1, r2, r3, r4, r5, a1, a2, hrand, hsp]
  change [word s.mem (stackArg s 3) 0, word s.mem (stackArg s 3) 8,
    word s.mem (stackArg s 3) 16, word s.mem (stackArg s 3) 24] =
      [word t.mem (stackArg t 3) 0, word t.mem (stackArg t 3) 8,
        word t.mem (stackArg t 3) 16, word t.mem (stackArg t 3) 24] at hw
  have hcounter : s.mem.readW (stackArg s 3) 64 = t.mem.readW (stackArg t 3) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  unfold searchOfState
  congr 1
  exact congrArg BitVec.toNat hcounter

theorem search_constantTime (v : RoundImpl) :
    ConstantTime isa searchContract.pre searchContract.pub (searchCode v) := by
  refine RelCT.constantTime ((search_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨searchOfState s, ⟨hs, rfl⟩, ht, (search_public_descriptor hp).symm⟩

end VG.Proof.Ffdh.X86_64.Generation
