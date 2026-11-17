import Tazuna.Data.Names
import Tazuna.Service.Message

/-! The diff tests compare these constructor values with the TS types. -/

def limits : List Tazuna.Service.Limit := samples% Tazuna.Service.Limit

def rejectionKinds : List Tazuna.Data.RejectionKind := samples% Tazuna.Data.RejectionKind
