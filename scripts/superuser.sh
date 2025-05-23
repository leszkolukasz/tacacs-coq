USERNAME="user1"
PASSWORD="pass1"
USERNAME_LEN=$(printf "%s" "$USERNAME" | wc -c)
PASSWORD_LEN=$(printf "%s" "$PASSWORD" | wc -c)

{
  printf '\x80'                                       # Version (128)
  printf '\x06'                                       # Type (SSUPERUSER)
  printf '\x00\x02'                                   # Nonce (2)
  printf "%02x" "$USERNAME_LEN" | xxd -r -p           # Username length
  printf "%02x" "$PASSWORD_LEN" | xxd -r -p           # Password length
  printf '\x00'                                       # Response (0)
  printf '\x00'                                       # Reason (0)
  printf '\x00\x00\x00\x00'                           # Result1
  printf '\x12\x23\x34\x45'                           # Destination IP
  printf '\x0A\x00'                                   # Destination Port
  printf '\x00\x01'                                   # Line (1)
  printf '\x00\x00\x00\x00'                           # Result2
  printf '\x00\x00'                                   # Result3
  printf "%s" "$USERNAME"                             # Username data
  printf "%s" "$PASSWORD"                             # Password data
} | nc -u -w1 localhost 3000
