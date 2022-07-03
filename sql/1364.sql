SELECT  i.invoice_id
       ,c.customer_name
       ,i.price
       ,COUNT(distinct ct.contact_name) AS contacts_cnt
       ,COUNT(distinct cc.email)        AS trusted_contacts_cnt
FROM invoices AS i
INNER JOIN customers AS c
ON c.customer_id = i.user_id
LEFT JOIN contacts AS ct
ON ct.user_id = c.customer_id
LEFT JOIN customers AS cc
ON cc.email = ct.contact_email
GROUP BY  i.invoice_id
         ,c.customer_name
         ,i.price
ORDER BY i.invoice_id asc