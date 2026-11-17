import Tazuna.Service.Basic
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Chart.Basic

namespace Tazuna.Thm.Service.Basic

open Tazuna.Data Tazuna.Service Tazuna.Spec
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Basic

theorem chart_of_definition (j : Structure) (service : String) (st : Tazuna.Service)
    (h : Tazuna.Service.ofStructure j service = .ok st)
    (c : Tazuna.Service.Chart) (hc : c ∈ st.charts) :
    ∃ d ∈ j.definitions, ∃ sc, d.chart? = some sc ∧ d.service = service ∧ c.name = d.name ∧ c.screen = d.isScreen ∧
      c.opened = (d.isScreen && j.isOpenedByScreen d.ref) := by
  unfold Tazuna.Service.ofStructure at h
  dsimp only at h
  obtain ⟨cs, hcs, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  cases h
  obtain ⟨_, hm, hx⟩ := mem_mapM_ok hcs hc
  obtain ⟨_, hd, he⟩ := List.mem_filterMap.mp hm
  obtain ⟨sc, hsc, rfl⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨hn, hs, ho⟩ := ofSpec_ok _ _ _ _ _ _ _ hx
  obtain ⟨hz, hsv⟩ := List.mem_filter.mp hd
  exact ⟨_, List.fst_mem_of_mem_zipIdx hz, sc, hsc, by simpa using hsv, hn, hs, ho⟩

end Tazuna.Thm.Service.Basic
