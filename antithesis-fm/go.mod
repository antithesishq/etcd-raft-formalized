module etcd-raft-formalized

go 1.26

replace go.etcd.io/raft/v3 => ..

replace tracekit => ./tracekit/go

require (
	github.com/antithesishq/antithesis-sdk-go v0.8.0
	go.etcd.io/bbolt v1.4.1
	go.etcd.io/raft/v3 v3.0.0
	google.golang.org/protobuf v1.36.12
	tracekit v0.0.0
)

require golang.org/x/sys v0.29.0
