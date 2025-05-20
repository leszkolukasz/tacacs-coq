USERNAME="user"
PASSWORD="pass"
USERNAME_LEN=$(printf "%s" "$USERNAME" | wc -c)
PASSWORD_LEN=$(printf "%s" "$PASSWORD" | wc -c)

{
  printf '\x80'                    # Version (128)
  printf '\x01'                    # Type (LOGIN)
  printf '\x00\x01'                # Nonce (1)
  printf "\\x%02x" "$USERNAME_LEN" # Username length
  printf "\\x%02x" "$PASSWORD_LEN" # Password length
  printf '\x00'                    # Response (0)
  printf '\x00'                    # Reason (0)
  printf '\x00\x00\x00\x00'        # Result1
  printf '\x00\x00\x00\x00'        # Destination IP
  printf '\x00\x00'                # Destination Port
  printf '\x00\x00'                # Line (0)
  printf '\x00\x00\x00\x00'        # Result2
  printf '\x00\x00'                # Result3
  printf "%s" "$USERNAME"          # Username data
  printf "%s" "$PASSWORD"          # Password data
} | nc -u -w1 localhost 3000
