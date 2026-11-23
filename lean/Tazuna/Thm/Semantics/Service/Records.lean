import Tazuna.Semantics.Service.Records

namespace Tazuna.Thm.Semantics.Service.Records

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service

def KeysDistinct (records : Records) : Prop := (records.map fun r => (r.entity, r.key)).Nodup

end Tazuna.Thm.Semantics.Service.Records
