import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Weierstrass.Unch

/-!
# Memory unchanged outside a list of ranges, on AArch64

What the field operations and programs change (`OpKeep.unch`,
`ProgKeep.unch`), as `Unch`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont

theorem _root_.VG.Proof.Mont.AArch64.OpKeep.unch {M : Mod} {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeep M base o s s') : Unch base [(o, 8 * M.n), (M.tmp, 8 * M.n)] s.mem s'.mem :=
  fun x hx => h.mem x (hx _ (List.mem_cons_self ..)) (hx (M.tmp, 8 * M.n) (by simp))

theorem _root_.VG.Proof.Mont.AArch64.OpKeep.scr {M : Mod} {base : Addr} {o size : Nat} {s s' : State}
    (h : OpKeep M base o s s') (hs : Scr s base size) : Scr s' base size :=
  ⟨(h.gpr _ (x0_not_clob' _)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap, hs.enc⟩

theorem ProgKeep.unch {M : Mod} {base : Addr} {W : List Nat} {s s' : State}
    (h : ProgKeep M base W s s') :
    Unch base (W.map (·, 8 * M.n) ++ [(M.tmp, 8 * M.n)]) s.mem s'.mem :=
  fun x hx => h.mem x (fun _ hw => hx _ (List.mem_append_left _ (List.mem_map_of_mem hw)))
    (hx _ (List.mem_append_right _ (List.mem_singleton_self _)))

end VG.Proof.Weierstrass.AArch64
