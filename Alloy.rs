// Definisi entitas
abstract sig User {}
sig Customer extends User {}
sig Merchant extends User {}

sig CreditCard {
  owner: Customer,
  limit: Int,
  balance: Int
}

sig Transaction {
  payer: Customer,
  payee: Merchant,
  amount: Int,
  paymentType: one PaymentType,
  status: one TransactionStatus,
  timestamp: Time // Waktu transaksi
}

sig TransactionStatus {
  success, failure
}

sig PaymentType {
  credit: one Transaction,
  debit: one Transaction
}

sig BankAPI {
  validateTransaction: Transaction -> TransactionStatus,
  processPayment: Transaction -> TransactionStatus
}

sig Session {
  user: User,
  token: lone Token,
  startTime: Time,
  endTime: Time
}

sig Token {
  user: User,
  value: Int,
  expirationTime: Time
}

sig Security {
  isAuthorized: User -> Bool,
  encryptData: Int -> Int,
  decryptData: Int -> Int
}

sig Log {
  logType: one LogType,
  content: String,
  timestamp: Time
}

sig LogType {
  info, error, audit
}

sig Notification {
  user: User,
  content: String,
  timestamp: Time
}

sig Cancellation {
  transaction: Transaction,
  reason: String,
  timestamp: Time
}

sig ThirdPartyService {
  integrate: one ServiceType -> Bool
}

sig ServiceType {
  paymentGateway, identityVerification, fraudDetection
}

// Aturan atau properti sistem
fact SufficientBalance {
  all t: Transaction |
    t.payer.creditCard.balance >= t.amount
}

fact CreditLimit {
  all c: CreditCard |
    c.balance <= c.limit
}

fact ValidSession {
  all s: Session |
    s.endTime >= s.startTime
}

fact ValidToken {
  all t: Token |
    t.expirationTime >= t.user.session.startTime and t.expirationTime <= t.user.session.endTime
}

fact AuthorizedTransaction {
  all t: Transaction |
    Security.isAuthorized[t.payer] and Security.isAuthorized[t.payee]
}

fact SecureData {
  all d: Int |
    Security.decryptData[Security.encryptData[d]] = d
}

fact LogTimestamp {
  all l: Log |
    l.timestamp >= l.logType.timestamp
}

fact NotificationTimestamp {
  all n: Notification |
    n.timestamp >= n.user.session.startTime and n.timestamp <= n.user.session.endTime
}

// Contoh instance
run {
  // Definisi beberapa pengguna, kartu kredit, transaksi, BankAPI, dan fitur lainnya
  some c1, c2: Customer |
  some m1: Merchant |
  some cc1: CreditCard | cc1.owner = c1 and cc1.limit = 1000 and cc1.balance = 500 |
  some cc2: CreditCard | cc2.owner = c2 and cc2.limit = 2000 and cc2.balance = 1500 |
  some t_success: Transaction | t_success.payer = c1 and t_success.payee = m1 and t_success.amount = 200 and t_success.paymentType = (credit + debit) and t_success.status = success and t_success.timestamp = 20231123 |
  some t_failure: Transaction | t_failure.payer = c2 and t_failure.payee = m1 and t_failure.amount = 1000 and t_failure.paymentType = (credit + debit) and t_failure.status = failure and t_failure.timestamp = 20231124 |
  some pt1, pt2: PaymentType | t_success.paymentType = pt1 and t_failure.paymentType = pt2 |
  some s1, s2: TransactionStatus | t_success.status = s1 and t_failure.status = s2 |
  some bankAPI: BankAPI | all t: Transaction | bankAPI.validateTransaction[t] = s1 and bankAPI.processPayment[t] = s2 |
  some session1: Session | session1.user = c1 and session1.token = one Token and session1.startTime = 20231123 and session1.endTime = 20231124 |
  some token1: Token | token1.user = c1 and token1.value = 123456 and token1.expirationTime = 20231124 |
  some security: Security | all u: User | security.isAuthorized[u] = true and security.encryptData[123] = 456 and security.decryptData[456] = 123 |
  some log1: Log | log1.logType = info and log1.content = "Transaction processed successfully." and log1.timestamp = 20231123 |
  some notification1: Notification | notification1.user = c1 and notification1.content = "Your payment was successful." and notification1.timestamp = 20231123 |
  some cancellation1: Cancellation | cancellation1.transaction = t_failure and cancellation1.reason = "Insufficient funds." and cancellation1.timestamp = 20231124 |
  some thirdPartyService: ThirdPartyService | thirdPartyService.integrate[paymentGateway] = true
}

run PaymentScenario for 5
