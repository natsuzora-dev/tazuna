import Tazuna.Service.Records

namespace Tazuna.Thm.Service.Records

open Tazuna.Data Tazuna.Service

def KeysDistinct (records : Records) : Prop := (records.map fun r => (r.entity, r.key)).Nodup

end Tazuna.Thm.Service.Records
