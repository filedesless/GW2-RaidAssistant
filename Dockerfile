from python

RUN mkdir /app
COPY requirements.txt /app/requirements.txt
RUN pip3 install -r /app/requirements.txt

WORKDIR /app
COPY src .

CMD ["python3", "raid_assistant.py"]

