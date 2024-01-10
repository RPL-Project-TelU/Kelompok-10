// Signatures
one sig Text {}
one sig EncryptedText {}

sig User {
  userId: Int,
  userName: Text,
  password: EncryptedText,
 criteria: Int,
 criteriaCurrency: Text,
 email: Text
}

sig CreditCard {
  number: Int,
  expiryDate: Int,
  cvv: Int,
  user: one User,
  limit: Int,
  currentBalance: Int
}

sig Item {
  name: Text,
  price: Int,
  quantityInStock: Int
}

sig Order {
  items: some Item,
  totalPrice: Int,
  paymentMethod: one PaymentMethod
}

sig PaymentMethod {
  kind: CreditCard
}

sig CashPayment {}
sig CreditPayment {
  card: one CreditCard
}

// Facts
fact UserHasCreditCard {
  User in CreditCard.user
}

fact OrderHasPaymentMethod {
  all o: Order | one p: PaymentMethod | o.paymentMethod = p
}


fact PaymentMethodKind {
  all p: PaymentMethod | p.kind in CreditCard + CashPayment
}

fact CreditPaymentHasCard {
  all p: CreditPayment | p.card in CreditCard
}

fact CreditCardPaymentLimit {
  all p: CreditPayment | all o: Order | p.card.currentBalance + o.totalPrice <= p.card.limit
}

fact OrderItemQuantityConstraint {
  all o: Order, i: o.items | i.quantityInStock >= 1
}

// Assertions
pred CreditLimitRespected {
  all p: CreditPayment | all o: Order | p.card.currentBalance + o.totalPrice <= p.card.limit
}

assert NoCreditPurchasesWhenMaxedOut {
  all u: CreditCard | all o: Order |
    o.totalPrice > u.limit
}

pred ItemsInStock {
  all o: Order | all i: o.items | i.quantityInStock > 0
}

// Commands
run CreditLimitRespected for 2 Order, 2 User, 2 CreditCard, 1 CashPayment, 1 CreditPayment, 3 Item, 2 PaymentMethod
check NoCreditPurchasesWhenMaxedOut
run ItemsInStock for 4 Order, 5 Item
