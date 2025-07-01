## TACACS protocol in Coq

Implementation of the TACACS protocol in Coq and Ocaml. According to the [RFC1492](https://datatracker.ietf.org/doc/html/rfc1492).

### Commands

- `make` - Build the project
- `make coq` - Build coq files
- `make clean` - Clean the project
- `make format` - Format the files

### Example usage

#### Server

```
dune exec ./src/server.exe -- -h localhost   
```

starts the server on `localhost` at port `3000`.

#### Client

```
dune exec ./src/client.exe -- -h localhost -p 3000 session login user1 pass1 
```

starts the client, connects to the server at `localhost:3000`, and enters a session loop.

The available users are:
- `user1` with password `pass1` (superuser)
- `user2` with password `pass2`

### Notes

- `coq` folder needs to be opened in separate VSCode window to handle imports correctly